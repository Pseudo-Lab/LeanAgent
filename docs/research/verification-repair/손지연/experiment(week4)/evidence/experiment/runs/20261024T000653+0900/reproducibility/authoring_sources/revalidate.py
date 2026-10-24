"""V-C fresh Lean, separate from pure replay; retain metric-specific differences."""
import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
import fcntl
import statistics
from common import read,write,run_dir,sha,log
from tasks import task,base_env,backend,make
from prepare import inventory

def diagnostics(value):
    # Ephemeral evaluator paths/coordinates may differ. Keep exact and content comparisons.
    return [dict(severity=d.get('severity'),message=d.get('message')) for d in value.get('diagnostics',[])]

def compare(old,actual):
    def optional(a,b):return None if a is None or b is None else a==b
    return dict(status=actual['status']==old['status'],proof_sha256=actual['candidate_hash']==old['candidate_hash'],
        axioms=optional(actual['axioms'],old['axioms']),diagnostics_exact=actual['diagnostics']==old['diagnostics'],
        diagnostic_messages=diagnostics(actual)==diagnostics(old),proof_tokens=optional(actual['metrics'].get('proof_tokens'),old['metrics'].get('proof_tokens')),
        raw_heartbeats=optional(actual['metrics'].get('raw_heartbeats'),old['metrics'].get('raw_heartbeats')),environment_id=actual['environment_id']==old['environment_id'])

def verify(job):
    key,p,env,body,old,kind=job;dest=run_dir()/'revalidation'/f'P{p}'/key/env['id']
    resultfile=dest/'comparison.json';dest.mkdir(parents=True,exist_ok=True)
    with (dest/'execution.lock').open('a') as lock:
        try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:return None
        if resultfile.exists():return read(resultfile)
        if env['id']==base_env(p)['id']:
            t=task(p);cal=read(run_dir()/'calibration'/f'P{p}.json');snapshot=cal['environment'];eid=cal['environment_id']
        else:
            t=make(p,env);cal=read(run_dir()/'holdout_calibration'/f'P{p}'/f"{env['id']}.json")
            if not cal['ready']:return None
            snapshot=cal['environment_snapshot'];eid=cal['environment_id']
        trace,runner,v=backend(dest/'fresh',t);v.environment=snapshot;v.environment_id=eid
        actual=v.verify(body,'saved_candidate',kind).to_dict()
        fields=compare(old,actual)
        value=dict(problem=p,environment=env['id'],proof_sha256=sha(body),original_check_kind=kind,fields=fields,
            semantic_match=all(fields[k] is not False for k in ('status','proof_sha256','axioms','environment_id')),
            all_available_fields_match=all(v is not False for v in fields.values()),old=old,actual=actual,new_model_calls=0)
        write(resultfile,value);log('fresh_revalidation',problem=p,environment=env['id'],proof=sha(body)[:12],semantic=value['semantic_match'],fields=fields)
        return value

def collect():
    envs=inventory();jobs={}
    for path in sorted((run_dir()/'runs').glob('*/*/*/*/*/result.json')):
        result=read(path);p=result['problem'];env=base_env(p)
        for cfile in sorted((path.parent/'candidates').glob('*/candidate.json')):
            c=read(cfile);old=c['verification'];body=c['body']
            if c['duplicate_cache']:
                # The underlying original reference is already included below.
                continue
            key=f"{c['proof_sha256']}-{old['check_kind']}"
            jobs.setdefault((p,env['id'],key),(key,p,env,body,old,old['check_kind']))
        if result.get('final_verification') and (path.parent/'selected.proof.lean').exists():
            body=(path.parent/'selected.proof.lean').read_text();old=result['final_verification'];key=f'{sha(body)}-final'
            jobs.setdefault((p,env['id'],key),(key,p,env,body,old,'final'))
    bodies={}
    for path in (run_dir()/'runs/P_A').glob('P*/normal/A*/repeat_*/config.json'):
        c=read(path)['original_candidate'];bodies[(read(path)['problem'],c['proof_sha256'])]=c['body']
    for path in (run_dir()/'runs/P_A').glob('P*/normal/A*/repeat_*/candidates/*/candidate.json'):
        c=read(path);p=int(path.parents[5].name[1:])
        bodies[p,c['proof_sha256']]=c['body']
    for path in sorted((run_dir()/'compatibility').glob('P*/*/*.json')):
        c=read(path);p=c['problem'];env=envs[c['environment']]
        # A prior timeout is an observation to compare, not a reason to omit this
        # saved proof from fresh Lean coverage. Keep the original result unchanged.
        if env['id']==base_env(p)['id']:continue
        old=c['result'];h=c['proof_sha256'];key=f'{h}-holdout'
        jobs.setdefault((p,env['id'],key),(key,p,env,bodies[p,h],old,'final'))
    return list(jobs.values())

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--workers',type=int,default=2);parser.add_argument('--summarize-only',action='store_true')
    parser.add_argument('--problems',type=int,nargs='+',help='Only schedule these problems; aggregate retains every recorded check.')
    args=parser.parse_args()
    if not args.summarize_only:
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures=[pool.submit(verify,j) for j in collect() if args.problems is None or j[1] in args.problems]
            for future in as_completed(futures):future.result()
    values=[dict(read(p),comparison_file=str(p.relative_to(run_dir()))) for p in sorted((run_dir()/'revalidation').glob('P*/*/*/comparison.json'))]
    for v in values:
        # Older raw records used None==None; aggregate only genuinely available measurements.
        v['fields']=compare(v['old'],v['actual'])
        v['semantic_match']=all(v['fields'][k] is not False for k in ('status','proof_sha256','axioms','environment_id'))
    keys=('status','proof_sha256','axioms','diagnostics_exact','diagnostic_messages','proof_tokens','raw_heartbeats','environment_id')
    summary=dict(unique_candidate_environment_checks=len(values),semantic_matches=sum(v['semantic_match'] for v in values),
        check_unit='problem, proof_sha256, environment, check_kind (candidate/final/holdout)',
        unique_problem_proof_environment_pairs=len({(v['problem'],v['proof_sha256'],v['environment']) for v in values}),
        field_matches={k:sum(v['fields'][k] is True for v in values) for k in keys},
        field_comparisons={k:sum(v['fields'][k] is not None for v in values) for k in keys},
        field_unavailable={k:sum(v['fields'][k] is None for v in values) for k in keys},new_model_calls=0,items=values)
    summary['optional_comparison_policy']='Compare values only when both observations exist; report availability changes separately. Raw comparison records are preserved.'
    summary['field_availability_changes']={
        'axioms':sum((v['old']['axioms'] is None)!=(v['actual']['axioms'] is None) for v in values),
        **{key:sum((v['old']['metrics'].get(key) is None)!=(v['actual']['metrics'].get(key) is None) for v in values)
            for key in ('proof_tokens','raw_heartbeats')}}
    differences=[]
    for v in values:
        old=v['old']['metrics'].get('raw_heartbeats');new=v['actual']['metrics'].get('raw_heartbeats')
        if old and new is not None:differences.append(100*(new-old)/old)
    summary['heartbeat_remeasurement_pct']=dict(n=len(differences),median=statistics.median(differences) if differences else None,
        median_absolute=statistics.median(map(abs,differences)) if differences else None,min=min(differences) if differences else None,max=max(differences) if differences else None)
    notable={}
    for field in ('status','proof_sha256','axioms','diagnostic_messages','proof_tokens','environment_id'):
        notable[field]=[dict(problem=v['problem'],environment=v['environment'],proof_sha256=v['proof_sha256'],
            old_status=v['old']['status'],actual_status=v['actual']['status'],comparison_file=v['comparison_file'])
            for v in values if v['fields'][field] is False]
    write(run_dir()/'analysis/revalidation_differences.json',notable)
    write(run_dir()/'analysis/lean_revalidation.json',summary);log('lean_revalidation_summary',checks=len(values),semantic_matches=summary['semantic_matches'])

if __name__=='__main__':main()
