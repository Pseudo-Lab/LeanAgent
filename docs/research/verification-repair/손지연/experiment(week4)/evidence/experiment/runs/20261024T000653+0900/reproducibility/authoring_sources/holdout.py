"""Evaluate byte-identical saved proofs in all designated environments, after freeze."""
import argparse
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor,as_completed
import fcntl
import math
from common import read,write,run_dir,sha,log
from tasks import make,task,base_env,backend
from prepare import inventory

def calibrate(p,env):
    path=run_dir()/'holdout_calibration'/f'P{p}'/f"{env['id']}.lock";path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        return _calibrate(p,env)

def _calibrate(p,env):
    path=run_dir()/'holdout_calibration'/f'P{p}'/f"{env['id']}.json"
    if path.exists():
        previous=read(path)
        if previous['ready']:return previous
        # Keep the failed adapter evidence; allow a repaired environment probe to be retried.
        archive=path.with_name(path.stem+'_previous.json')
        if not archive.exists():write(archive,previous)
    t=make(p,env);trace,runner,v=backend(run_dir()/'holdout_baseline'/f'P{p}'/env['id'],t)
    prep=v.prepare();write(trace.directory/'prepare.json',prep.to_dict())
    baseline=v.verify(t.initial_body,'baseline','reference') if prep.status=='candidate_pass' else prep
    value=dict(problem=p,environment=env,preparation=prep.to_dict(),verification=baseline.to_dict(),
        environment_snapshot=v.environment,environment_id=v.environment_id,ready=baseline.status=='candidate_pass')
    if value['ready']:
        cap=max(200000,math.ceil(1.25*baseline.metrics['heartbeats']));t.limits['max_heartbeats']=cap
        write(t.source.parent/'task.json',t.config);value['frozen_max_heartbeats']=cap
    write(path,value);log('holdout_baseline',problem=p,environment=env['id'],status=baseline.status);return value

def evaluate(p,env,proof_sha,body,origins):
    path=run_dir()/'compatibility'/f'P{p}'/proof_sha/f"{env['id']}.json";path.parent.mkdir(parents=True,exist_ok=True)
    with path.with_suffix('.lock').open('a') as lock:
        try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:return None
        if path.exists():return read(path)
        if env['id']==base_env(p)['id']:
            # This is the same environment and exact proof already independently checked in P-A.
            result=origins[0]['verification']
            value=dict(problem=p,environment=env['id'],proof_sha256=proof_sha,result=result,
                source='stored P-A base validation',model_calls=0,extra_lean=False,
                passed=result['status'] in ('candidate_pass','verified'),infrastructure_failure=False)
        else:
            if not (run_dir()/'preparation'/f"{env['id']}_ready.json").exists():return None
            calibration=calibrate(p,env)
            if not calibration['ready']:
                value=dict(problem=p,environment=env['id'],proof_sha256=proof_sha,result=calibration['verification'],
                    source='environment baseline failed before candidate test',model_calls=0,extra_lean=True,passed=None,infrastructure_failure=True)
            else:
                t=make(p,env);trace,runner,v=backend(run_dir()/'holdout_checks'/f'P{p}'/proof_sha/env['id'],t)
                v.environment=calibration['environment_snapshot'];v.environment_id=calibration['environment_id']
                result=v.verify(body,'holdout','final')
                value=dict(problem=p,environment=env['id'],proof_sha256=proof_sha,result=result.to_dict(),source='fresh unchanged-proof holdout',
                    model_calls=0,extra_lean=True,passed=result.status=='verified',
                    infrastructure_failure=result.status in ('environment_error','process_error','timeout','wall_time_limit'))
        write(path,value);log('compatibility',problem=p,environment=env['id'],proof=proof_sha[:12],passed=value['passed']);return value

def collect():
    candidates={}
    for resultfile in sorted((run_dir()/'runs/P_A').glob('P*/normal/A*/repeat_*/result.json')):
        history=resultfile.parent;result=read(resultfile);p=result['problem']
        if not (history/'selection_freeze.json').exists():raise RuntimeError('holdout before main selection freeze')
        config=read(history/'config.json');values=[config['original_candidate']]
        values.extend(read(path) for path in sorted((history/'candidates').glob('*/candidate.json')))
        for c in values:
            if not c['eligible']:continue
            key=p,c['proof_sha256']
            item=candidates.setdefault(key,dict(body=c['body'],origins=[]))
            if item['body']!=c['body']:raise AssertionError('hash collision')
            item['origins'].append(dict(history=str(history),call=c['call'],verification=c['verification']))
    return candidates

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--workers',type=int,default=2);parser.add_argument('--baseline-only',action='store_true')
    args=parser.parse_args();envs=inventory()
    if args.baseline_only:
        jobs=[(p,e) for e in envs.values() for p in e['problems'] if e['id']!=base_env(p)['id'] and (run_dir()/'preparation'/f"{e['id']}_ready.json").exists()]
        function=calibrate
    else:
        candidates=collect();write(run_dir()/'analysis/holdout_candidate_index.json',[dict(problem=p,proof_sha256=h,origins=v['origins']) for (p,h),v in candidates.items()])
        jobs=[(p,e,h,v['body'],v['origins']) for (p,h),v in candidates.items() for e in envs.values() if p in e['problems']]
        function=evaluate
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures={pool.submit(function,*job):job[:2] for job in jobs}
        for future in as_completed(futures):
            try:future.result()
            except Exception as exc:log('holdout_exception',job=futures[future],error=str(exc));raise

if __name__=='__main__':main()
