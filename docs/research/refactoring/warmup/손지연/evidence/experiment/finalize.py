"""Close a fully covered run, preserving accounting and resource limitations."""
import importlib.metadata
import difflib
from pathlib import Path
import subprocess
import sys
import time
from common import HERE,read,write,run_dir,sha,log
from holdout import collect as candidates
from prepare import inventory
from revalidate import collect as revalidation_jobs
from subscription import redact


def refresh(script,*args):
    subprocess.run([sys.executable,str(HERE/(script+'.py')),*args],check=True)


def export_lineage(run):
    """Human-reviewable diffs derived from frozen inputs; no inference changes."""
    index=[]
    for resultfile in sorted((run/'runs').glob('*/*/*/*/*/result.json')):
        history=resultfile.parent;config=read(history/'config.json')
        fresh=config['family']=='P_A' and config['condition'] in ('A0','A1')
        previous=config['initial_body'];previous_id='initial'
        for path in sorted((history/'candidates').glob('*/candidate.json')):
            c=read(path);parent=config['original_body'] if fresh else previous
            parent_id='original_input' if fresh else previous_id
            request=read(history/'model_calls'/f"{c['call']:02d}"/'request.json')
            if request['current_file']!=redact(config['prefix']+parent+config['suffix']):
                raise ValueError(f'Parent reconstruction disagrees with actual request: {path}')
            dest=run/'derived'/history.relative_to(run)/'candidate_diffs'/f"{c['call']:02d}.patch"
            dest.parent.mkdir(parents=True,exist_ok=True)
            delta=difflib.unified_diff(parent.splitlines(keepends=True),c['body'].splitlines(keepends=True),
                fromfile=parent_id+'.proof.lean',tofile=f"candidate_{c['call']:02d}.proof.lean")
            dest.write_text(''.join(line if line.endswith('\n') else line+'\n\\ No newline at end of file\n' for line in delta))
            index.append(dict(history=str(history.relative_to(run)),candidate_id=f"candidate_{c['call']:02d}",
                parent_candidate_id=parent_id,parent_proof_sha256=sha(parent),proof_sha256=c['proof_sha256'],
                diff=str(dest.relative_to(run)),derived_after_run=True))
            previous=c['body'];previous_id=f"candidate_{c['call']:02d}"
    write(run/'analysis/candidate_lineage.json',index)
    return len(index)


def main():
    run=run_dir()
    pipeline=run/'completion.json'
    if not pipeline.exists():raise SystemExit('Wait for finish.py before finalizing.')
    expected_pairs=[(p,h,e['id']) for (p,h) in candidates() for e in inventory().values() if p in e['problems']]
    missing_pairs=[k for k in expected_pairs if not (run/'compatibility'/f'P{k[0]}'/k[1]/f'{k[2]}.json').exists()]
    jobs=revalidation_jobs()
    missing_checks=[j[:3] for j in jobs if not (run/'revalidation'/f'P{j[1]}'/j[0]/j[2]['id']/'comparison.json').exists()]
    if missing_pairs or missing_checks:raise SystemExit(f'Incomplete coverage: {len(missing_pairs)} holdouts, {len(missing_checks)} fresh checks.')
    for script,args in [('revalidate',['--summarize-only']),('replay',[]),('controls',[]),('audit',[])]:refresh(script,*args)
    audit=read(run/'analysis/audit.json');replay=read(run/'analysis/record_replay.json');controls=read(run/'analysis/control_checks.json')
    histories=[read(p) for p in (run/'runs').glob('*/*/*/*/*/result.json')]
    p_expected={(p,c,r) for p in range(1,16) for c in ('A0','A1','A2','A3') for r in range(1,4)}
    v_expected={(p,e,c,r) for p in range(1,16) for e in ('proof_error','incomplete') for c in ('B1','B2') for r in range(1,4)}
    p_actual={(x['problem'],x['condition'],x['repeat']) for x in histories if x['family']=='P_A'}
    v_actual={(x['problem'],x['error_category'],x['condition'],x['repeat']) for x in histories if x['family']=='V_B'}
    integrity=not any(audit[k] for k in ('accounting_mismatches','tool_events','redaction_failures','duplicate_threads',
        'selected_file_hash_mismatches','saved_candidate_hash_mismatches','invocations_with_multiple_completed_turns',
        'initial_model_input_mismatches','v_feedback_input_pair_mismatches'))
    integrity=integrity and all(audit[k] for k in ('original_package_unchanged','dataset_unchanged','design_unchanged'))
    complete=(p_actual==p_expected and v_actual==v_expected and len(list((run/'V_A').glob('P*/*.json')))==90
        and replay['histories']==360 and replay['matched']==360 and controls['passed']==len(controls['checks'])
        and len(histories)==360 and audit['initial_model_inputs_checked']==360 and audit['v_feedback_input_pairs_checked']==90
        and controls['complete_scope'] and integrity)
    if not complete:raise SystemExit('Coverage or integrity failed; inspect audit, replay, controls before closing.')
    lineage_count=export_lineage(run)
    if not (run/'completion_pipeline.json').exists():write(run/'completion_pipeline.json',read(pipeline))
    result=read(pipeline)
    result.update(execution_complete=True,main_histories=len(histories),holdout_candidate_environment_pairs=len(expected_pairs),
        holdout_missing=[],revalidation_checks=len(jobs),revalidation_missing=0,integrity_audit_ok=integrity,
        model_usage_complete=not audit['in_flight_or_unknown'],soft_token_limits_all_satisfied=not audit['soft_token_budget_overruns'],
        total_model_tokens=audit['total_model_tokens'],known_model_tokens=audit['known_model_tokens'],
        candidate_lineage_records=lineage_count,
        unknown_usage_calls=len(audit['unknown_usage_calls']),api_spend_usd=None,usd3_strict_compliance=None,
        arena_closed_track_compliant=False,finalized_at=time.time())
    write(pipeline,result)
    state=read(run/'execution_state.json') if (run/'execution_state.json').exists() else {}
    state.update(updated_at=time.time(),phase='complete',remaining=[],active_logs=[],completed_model_histories=len(histories),
        compatibility_completed=len(expected_pairs),compatibility_expected=len(expected_pairs),
        revalidation_completed=len(jobs),revalidation_expected=len(jobs),completion_manifest='completion.json')
    write(run/'execution_state.json',state)
    source_manifest=[]
    for path in sorted(HERE.glob('*.py'))+[HERE/'README.md',HERE/'DESIGN.md']:
        dest=run/'reproducibility/authoring_sources'/path.name;dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(path.read_bytes());source_manifest.append(dict(file=path.name,sha256=sha(path.read_bytes()),snapshot=str(dest.relative_to(run))))
    versions={name:importlib.metadata.version(name) for name in ('matplotlib','Markdown')}
    write(run/'reproducibility/final_source_manifest.json',dict(files=source_manifest,python=sys.version,analysis_dependencies=versions,
        inference_sources='Per-history effective_runner.json and snapshots/runner_sources preserve the versions actually loaded by model workers.',
        original_package_unchanged=audit['original_package_unchanged']))
    refresh('analyze');refresh('figures');refresh('analyze')
    log('run_finalized',**result)


if __name__=='__main__':main()
