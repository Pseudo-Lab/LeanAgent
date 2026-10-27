"""Older Lean module headers disallow #print axioms; use the existing native audit."""
import json
from verifier import ExperimentVerifier
from lean_repair.diagnostics import source_header_end

class ModuleAuditVerifier(ExperimentVerifier):
    def _audit_suffix(self):
        target='_root_.'+self.task.config['target']
        return f'\n#check {target}\n#repair_axioms {target}\n'

    def _run(self,text,label,instrumented=False,heartbeat_limit=None):
        inserted=False;original=text
        if '#repair_axioms ' in text and 'namespace LeanRepairSupport' not in text:
            at=source_header_end(text[:self.task.declaration_start]);text=self._with_support(text)
            inserted=True;line_before=original[:at].count('\n')+1
            extra=text.count('\n')-original.count('\n')
        dest,proc,messages,unparsed=super()._run(text,label,instrumented,heartbeat_limit)
        if inserted:
            for message in messages:
                for key in ('position','end_position'):
                    position=message.get(key)
                    if position and position.get('line',0)>line_before+extra:
                        message[key]={**position,'line':position['line']-extra}
                    elif position and position.get('line',0)>line_before:
                        message[key]=None
                message['evaluator_header_inserted_lines']=extra
        return dest,proc,messages,unparsed

    def _axioms(self,messages):
        for diagnostic in reversed(messages):
            message=str(diagnostic['message'])
            if message.startswith('REPAIR_AXIOMS|'):
                value=json.loads(message.split('|',1)[1]);target=self.task.config['target']
                if value['target']==target or value['target'].startswith('_private.') and value['target'].endswith('.'+target):
                    return sorted(value['axioms'])
        return None
