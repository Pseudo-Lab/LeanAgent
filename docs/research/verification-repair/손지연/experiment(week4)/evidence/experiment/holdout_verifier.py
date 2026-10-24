"""Audit older module artifacts from a separate nonmodule file, without rewriting source."""
from pathlib import Path
from verifier import ExperimentVerifier
from common import write
from lean_repair.diagnostics import parse_cli_output

MARKER='-- EXPERIMENT_SEPARATE_AXIOM_AUDIT'

class ModuleAuditVerifier(ExperimentVerifier):
    def _audit_suffix(self):
        return '\n#check _root_.'+self.task.config['target']+'\n'+MARKER+'\n'

    def _run(self,text,label,instrumented=False,heartbeat_limit=None):
        if MARKER not in text:return super()._run(text,label,instrumented,heartbeat_limit)
        # Produce the original module's object as well as its ordinary compile diagnostics.
        original_run=self.runner.run
        def compile_object(argv,cwd,directory,timeout,stdin=None):
            argv=list(argv);output=Path(directory)/'candidate.olean'
            if argv[-1].endswith('candidate.lean'):
                argv=[('--root='+str(directory)) if arg.startswith('--root=') else arg for arg in argv]
                argv[-1:-1]=['-o',str(output)]
            return original_run(argv,cwd,directory,timeout,stdin)
        self.runner.run=compile_object
        try:dest,proc,messages,unparsed=super()._run(text,label,instrumented,heartbeat_limit)
        finally:self.runner.run=original_run
        if self._process_status(proc) or proc['returncode']!=0:return dest,proc,messages,unparsed
        prefix=['elan','run',self.task.config['pins']['toolchain'],'lake','env']
        if not hasattr(self,'_audit_search_path'):
            lookup=original_run(prefix+['printenv','LEAN_PATH'],self.task.project,dest/'audit_search_path',30)
            if lookup['returncode']!=0 or self._process_status(lookup):
                proc['process_error']='separate axiom audit search-path lookup failed';return dest,proc,messages,unparsed
            self._audit_search_path=Path(lookup['stdout']).read_text().strip()
        module='candidate'
        auditor=dest/'audit.lean'
        auditor.write_text('import Lean\nimport '+module+'\n#print axioms _root_.'+self.task.config['target']+'\n')
        auditdir=dest/'axiom_audit'
        audit=original_run(prefix+['env','LEAN_PATH='+self._audit_search_path+':'+str(dest),'lean','--json','--root='+str(self.out),str(auditor)],
            self.task.project,auditdir,self.task.limits['lean_seconds'])
        extra,other=parse_cli_output(Path(audit['stdout']).read_text(errors='replace'))
        for item in extra:
            item['separate_axiom_audit']=True
            item['audit_position']=item['position'];item['audit_end_position']=item['end_position']
            # Coordinates belong to audit.lean, not to the original theorem source.
            # Keep backend coordinates in raw/audit fields and prevent false source-span enrichment.
            item['position']=item['end_position']=None
        messages.extend(extra);unparsed.extend(other);proc['separate_axiom_audit_process']=audit
        if self._process_status(audit) or audit['returncode']!=0:
            proc['process_error']='separate module axiom audit failed'
        write(dest/'process.json',proc)
        return dest,proc,messages,unparsed
