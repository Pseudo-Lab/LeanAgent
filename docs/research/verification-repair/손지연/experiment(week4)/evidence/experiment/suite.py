"""Finite, lock-protected full dataset execution with durable per-history evidence."""
import argparse
from concurrent.futures import ThreadPoolExecutor,as_completed
import itertools
import time
import traceback
from common import read,write,run_dir,log
from engine import execute,history_path

def jobs(family,problems):
    conditions=['A0','A1','A2','A3'] if family=='P_A' else ['B1','B2']
    errors=[None] if family=='P_A' else ['proof_error','incomplete']
    # Repeat-major and problem-interleaved conditions to spread time/quota effects.
    for repeat in range(1,4):
        for p in problems:
            for error in errors:
                order=conditions if (p+repeat)%2==0 else list(reversed(conditions))
                for condition in order:yield family,p,condition,repeat,error

def main():
    parser=argparse.ArgumentParser();parser.add_argument('family',choices=['P_A','V_B']);parser.add_argument('--problems',type=int,nargs='+',default=list(range(1,16)));parser.add_argument('--workers',type=int,default=5);parser.add_argument('--wait-inputs',action='store_true')
    args=parser.parse_args();work=[j for j in jobs(args.family,args.problems) if not (history_path(*j)/'result.json').exists()]
    # Submit bounded batches: a quota/accounting stop must not create 180 fake failures.
    stop=False;finished=0
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        queue=work[:];pending={}
        def submit():
            for index,job in enumerate(queue):
                family,p,condition,repeat,error=job
                ready=(run_dir()/'calibration'/f'P{p}.json').exists() and (family=='P_A' or (run_dir()/'V_A'/f'P{p}'/f'{error}.json').exists())
                if ready or not args.wait_inputs:
                    queue.pop(index);pending[pool.submit(execute,*job)]=job;return True
            return False
        for _ in range(args.workers):submit()
        while pending or (queue and not stop):
            if not pending:
                time.sleep(15)
                for _ in range(args.workers):submit()
                continue
            done=next(as_completed(pending));job=pending.pop(done)
            try:
                result=done.result();finished+=1
                reason=result.get('stop_reason','')
                if reason in ('subscription_included_quota_limit','subscription_quota_unavailable','subscription_accounting_uncertain','interrupted_call_unknown_usage_or_output'):
                    stop=True;write(run_dir()/f'{args.family}_global_stop.json',dict(job=job,reason=reason,remaining_not_executed=True))
            except Exception as exc:
                log('history_exception',job=job,error=str(exc));write(history_path(*job)/'exception.json',dict(error=str(exc),traceback=traceback.format_exc()))
                stop=True
            if not stop:
                while len(pending)<args.workers and submit():pass
    log('suite_returned',family=args.family,finished_this_process=finished,global_stop=stop)

if __name__=='__main__':main()
