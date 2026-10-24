"""V-C exact record replay: reads saved records; never starts Lean or a model."""
from collections import Counter
import json
from common import read,write,run_dir,sha,log
from engine import initial_state,make_request,update_state,choose,rank,INFRA
from audit import effective_sources,INITIAL_ENGINE

def replay(path):
    config=read(path/'config.json');original=[config['original_candidate']] if config['family']=='P_A' else []
    candidates=original[:];state=initial_state(config);seen=Counter();best=choose(candidates)
    differences=[];requests=0;final=None;selected=None;stop=None;last_budget=None;terminal=None;freeze=[]
    for event in [json.loads(line) for line in (path/'events.jsonl').read_text().splitlines()]:
        kind=event['event']
        if kind=='request':
            requests+=1;expected=make_request(config,state)
            if expected!=event['payload']:differences.append(f'request_{event["call"]}')
            if sha(json.dumps(expected,ensure_ascii=False))!=event['payload_sha256']:differences.append(f'request_hash_{event["call"]}')
            saved=path/'model_calls'/f'{event["call"]:02d}'/'request.json'
            if saved.exists() and expected!=read(saved):differences.append(f'outbound_bytes_{event["call"]}')
        elif kind=='model_response':last_budget=event['budget']
        elif kind=='model_error':stop=event['reason'];last_budget=event['budget']
        elif kind=='candidate':
            c=event['candidate'];candidates.append(c);seen[c['proof_sha256']]+=1;best=choose(candidates)
            state=update_state(config,state,c,best);last_budget=event['budget']
            if state!=event['state']:differences.append(f'state_{c["call"]}')
            if (best['proof_sha256'] if best else None)!=event['best_sha256']:differences.append(f'best_{c["call"]}')
            if c['verification']['status'] in INFRA:stop=c['verification']['status']
        elif kind=='final_rejected':
            c=event['candidate'];candidates=[c if item['call']==c['call'] and item['origin']=='generated' else item for item in candidates]
            best=choose(candidates);state=update_state(config,state,c,best)
            if state!=event['state']:differences.append(f'final_rejected_state_{c["call"]}')
        elif kind=='selection_freeze':
            freeze=[c['proof_sha256'] for c in sorted([c for c in candidates if c['eligible']],key=rank)]
            if freeze!=event['ranked_hashes']:differences.append('selection_freeze')
        elif kind=='final_verification':
            if event['result']['status']=='verified':
                final=event['result'];selected=event['proof_sha256']
                if config['family']=='V_B':stop='verified'
        elif kind=='terminal':terminal=event['result']
    if terminal is None:return dict(path=str(path),match=False,differences=['missing_terminal'],new_model_calls=0,new_lean_calls=0)
    if stop is None:
        effective=read(path/'effective_runner.json')['effective_engine_sha256'] if (path/'effective_runner.json').exists() else read(path/'run_manifest.json')['adapter_hashes']['engine.py']
        if any(n>=2 for n in seen.values()) and (state['completed_calls']<config['max_calls'] or effective!=INITIAL_ENGINE):stop='repeated_candidate'
        elif terminal['stop_reason']=='wall_time_limit':
            # Elapsed boundary is a stored terminal event, not a live clock measurement.
            stop='wall_time_limit'
        else:stop='one_shot_complete' if config['family']=='P_A' and config['condition']=='A0' else 'search_call_limit' if config['family']=='P_A' else 'repair_limit'
    if stop!=terminal['stop_reason']:differences.append('stop_reason')
    if selected!=terminal['selected_sha256']:differences.append('selected_sha256')
    if bool(final and final['status']=='verified')!=terminal['verified']:differences.append('verified')
    ledger=read(path/'model_ledger.json') if (path/'model_ledger.json').exists() else None
    if ledger:
        entries=ledger['entries'];known=sum((entry.get('usage') or {}).get('input_tokens',0)+(entry.get('usage') or {}).get('output_tokens',0) for entry in entries)
        if known!=terminal['budget']['tokens']:differences.append('model_tokens')
        if len(entries)!=terminal['budget']['calls']:differences.append('model_calls')
        if last_budget and last_budget!=terminal['budget']:differences.append('budget_snapshot')
    if config['family']=='P_A' and (path/'selection_freeze.json').exists():
        if read(path/'selection_freeze.json')['ranked_hashes']!=freeze:differences.append('freeze_file')
    return dict(path=str(path),family=config['family'],problem=config['problem'],condition=config['condition'],repeat=config['repeat'],
        requests=requests,match=not differences,differences=differences,replayed_stop=stop,replayed_selected=selected,
        new_model_calls=0,new_lean_calls=0,stored_elapsed_events=True)

def main():
    effective_sources()
    values=[replay(path.parent) for path in sorted((run_dir()/'runs').glob('*/*/*/*/*/result.json'))]
    value=dict(histories=len(values),matched=sum(v['match'] for v in values),new_model_calls=0,new_lean_calls=0,items=values)
    write(run_dir()/'analysis/record_replay.json',value);log('record_replay',histories=len(values),matched=value['matched'])

if __name__=='__main__':main()
