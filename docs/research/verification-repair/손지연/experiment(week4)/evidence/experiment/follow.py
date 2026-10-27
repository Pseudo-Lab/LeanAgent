"""Read-only status, including live usage and completion by problem."""
from collections import Counter
from datetime import datetime
from common import read,run_dir

def main():
    root=run_dir();results=[read(p) for p in (root/'runs').glob('*/*/*/*/*/result.json')]
    print('Run:',root.name)
    print('Base:',len(list((root/'calibration').glob('P*.json'))),'/ 15; env:',len(list((root/'preparation').glob('*_ready.json'))),'/ 15')
    for family in ('P_A','V_B'):
        values=[r for r in results if r['family']==family]
        print(family,len(values),'/ 180; verified:',sum(r['verified'] for r in values),'stops:',dict(Counter(r['stop_reason'] for r in values)))
        print('  Per problem:',dict(sorted(Counter(r['problem'] for r in values).items())))
    print('V_A:',len(list((root/'V_A').glob('P*/*.json'))),'/ 90')
    records=[read(p) for p in (root/'runs').glob('*/*/*/*/*/model_ledger.json')]
    ledgers=[r['snapshot'] for r in records]
    print('Calls:',sum(x['calls'] for x in ledgers),'known tokens:',sum(x['tokens'] for x in ledgers),
        'in-flight calls:',sum(e['state']=='in_flight' for r in records for e in r['entries']),
        'unknown-usage calls:',sum(e['state']=='unknown_usage' for r in records for e in r['entries']))
    print('History exceptions:',len(list((root/'runs').glob('*/*/*/*/*/exception.json'))))
    index=root/'analysis/holdout_candidate_index.json'
    if index.exists():
        from prepare import inventory
        expected=sum(sum(c['problem'] in e['problems'] for e in inventory().values()) for c in read(index))
        print('Compatibility:',len(list((root/'compatibility').glob('P*/*/*.json'))),'/',expected)
    if len(results)==360:
        from revalidate import collect
        jobs=collect();covered=sum((root/'revalidation'/f'P{j[1]}'/j[0]/j[2]['id']/'comparison.json').exists() for j in jobs)
        print('Fresh verifier checks:',covered,'/',len(jobs))
        files=list((root/'revalidation').glob('P*/*/*/comparison.json'))
        if files:
            latest=max(files,key=lambda p:p.stat().st_mtime)
            print('  Latest:',latest.parts[-4],latest.parts[-2],datetime.fromtimestamp(latest.stat().st_mtime).astimezone().isoformat(timespec='seconds'))
    completion=root/'completion.json'
    print('Execution complete:',read(completion).get('execution_complete',False) if completion.exists() else False)

if __name__=='__main__':main()
