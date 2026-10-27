"""Durable postprocessing pipeline; waits for authorised inference, then finishes P-B/C and V-C."""
import os
from pathlib import Path
import subprocess
import sys
import time
from common import HERE,read,write,append,run_dir,log

def count(family):return len(list((run_dir()/'runs'/family).glob('P*/*/*/*/result.json')))

def run(script,*args):
    started=time.time();path=HERE/f'pipeline-{script}.log'
    with path.open('a') as stream:
        proc=subprocess.run([sys.executable,str(HERE/(script+'.py')),*map(str,args)],cwd=HERE.parent.parent,stdout=stream,stderr=subprocess.STDOUT)
    append(run_dir()/'pipeline_events.jsonl',dict(script=script,args=args,returncode=proc.returncode,started_at=started,finished_at=time.time(),log=str(path)))
    if proc.returncode:raise RuntimeError(f'{script} failed; see {path}')

def wait_for(family):
    while count(family)<180:
        if (run_dir()/f'{family}_global_stop.json').exists():
            raise RuntimeError(f'{family} stopped before full scope; inspect global_stop and recover rather than claiming completion')
        run('analyze');time.sleep(30)

def main():
    wait_for('P_A')
    run('holdout','--workers',4)
    wait_for('V_B')
    while len(list((run_dir()/'V_A').glob('P*/*.json')))<90:time.sleep(15)
    run('replay');run('controls')
    from revalidate import collect
    while True:
        run('revalidate','--workers',4)
        jobs=collect()
        missing=[j for j in jobs if not (run_dir()/'revalidation'/f'P{j[1]}'/j[0]/j[2]['id']/'comparison.json').exists()]
        if not missing:break
        time.sleep(15)
    run('audit');run('analyze');run('figures')
    replay=read(run_dir()/'analysis/record_replay.json');audit=read(run_dir()/'analysis/audit.json')
    controls=read(run_dir()/'analysis/control_checks.json')
    index=read(run_dir()/'analysis/holdout_candidate_index.json')
    from prepare import inventory
    expected=[(c['problem'],c['proof_sha256'],e['id']) for c in index for e in inventory().values() if c['problem'] in e['problems']]
    missing=[list(k) for k in expected if not (run_dir()/'compatibility'/f'P{k[0]}'/k[1]/f'{k[2]}.json').exists()]
    result=dict(main_histories=count('P_A')+count('V_B'),V_A_cases=len(list((run_dir()/'V_A').glob('P*/*.json'))),
        replay_histories=replay['histories'],replay_matches=replay['matched'],holdout_candidate_environment_pairs=len(expected),
        holdout_missing=missing,revalidation_checks=len(jobs),controls_passed=controls['passed'],controls_complete_scope=controls['complete_scope'],
        audit_ok=not any(audit[k] for k in ('accounting_mismatches','tool_events','redaction_failures','duplicate_threads','in_flight_or_unknown')),
        original_package_unchanged=audit['original_package_unchanged'],finished_at=time.time())
    result['execution_complete']=result['main_histories']==360 and result['V_A_cases']==90 and not missing
    write(run_dir()/'completion.json',result);run('analyze');log('pipeline_complete',**result)

if __name__=='__main__':main()
