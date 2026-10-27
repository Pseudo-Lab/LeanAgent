"""Search/repair controller with an explicit best-so-far and replayable requests."""
from collections import Counter
import fcntl
import json
from pathlib import Path
import time
from common import HERE, read, write, append, sha, run_dir, log, package_hashes
from tasks import task, backend
from subscription import Budget, CodexModel, redact
from lean_repair.model import ModelError

INFRA={'environment_error','process_error','timeout','wall_time_limit'}
CONSTRAINTS=[
    'Return exactly diagnosis and proof_body as JSON strings; proof_body is one complete by proof.',
    'Only the designated proof body may change. Preserve every declaration, statement, assumption, import and surrounding source byte.',
    'No sorry/admit, new axioms, unsafe code, metaprogramming, IO, commands or resource-option changes.',
    'Ordinary local have proofs and ordinary mathematical constants are allowed.'
]

def metrics(value,baseline):
    m=value.get('metrics',{})
    t,h=m.get('proof_tokens'),m.get('raw_heartbeats')
    t0,h0=baseline.get('proof_tokens'),baseline.get('raw_heartbeats')
    rt=100*(1-t/t0) if t0 and t is not None else None
    rh=100*(1-h/h0) if h0 and h is not None else None
    return dict(proof_tokens=t,raw_heartbeats=h,token_reduction_pct=rt,heartbeat_reduction_pct=rh,
        search_score=(rt+rh)/2 if rt is not None and rh is not None else None)

def rank(candidate):
    m=candidate['measurement']
    return (-m['search_score'],m['proof_tokens'],m['raw_heartbeats'],candidate['proof_sha256'])

def choose(candidates):
    valid=[c for c in candidates if c['eligible']]
    return min(valid,key=rank) if valid else None

def facts(result):
    value={k:result.get(k) for k in ('diagnostics','goals','local_context','sorries','axioms','detail')}
    path=result.get('raw_log_path')
    value['raw_lean_output']=Path(path).read_text(errors='replace') if path else None
    return redact(value)

def make_request(config,state):
    """Pure request formatter: works identically with stored facts in record replay."""
    p=config['family']=='P_A';condition=config['condition']
    fresh=p and condition in ('A0','A1')
    body=config['original_body'] if fresh else state['current_body']
    payload=dict(target=config['target'],current_file=config['prefix']+body+config['suffix'],
        constraints=CONSTRAINTS,remaining_proposals=config['max_calls']-state['completed_calls'])
    if p:
        payload['objective']='Refactor this normal Lean proof to reduce proof syntax tokens and elaboration heartbeats. Keep it complete and fixed-statement valid.'
        payload['guidance']='Produce a fresh refactoring from the original proof.' if fresh else 'Improve the current proof; repair any compilation failure. Continue looking for better proofs even after a valid result.'
        if not fresh:
            f=state['facts']
            payload['feedback']='\n\n'.join(json.dumps(v,ensure_ascii=False) for v in f.values()) if f else None
            payload['previous_diagnoses']=state['diagnoses']
        if condition=='A3':
            payload['metric_feedback']=dict(current=state['current_measurement'],best=state['best_measurement'],
                baseline=config['baseline_metrics'],search_score='(token_reduction_pct+heartbeat_reduction_pct)/2; no compatibility or holdout feedback')
    else:
        payload['objective']='Repair the damaged proof. The normal reference proof is hidden. Close all goals and produce a complete proof.'
        f=state['facts']
        if condition=='B1':
            payload['feedback']='\n\n'.join(json.dumps(v,ensure_ascii=False) for v in f.values())
            payload['guidance']='Correct the proof using the compiler feedback and retry.'
        else:
            payload['feedback']=dict(status=state['status'],**f)
            payload['guidance']={'proof_error':'Repair the failed tactic using expected/actual types, goals and local context.',
                'incomplete':'Close every remaining goal and remove every sorry dependency.',
                'invalid_candidate':'Return one valid complete by proof inside the fixed boundary.',
                'resource_limit':'Reduce elaboration work without changing resource options.'}.get(state['status'],'Use the classified feedback to repair the proof.')
        payload['previous_diagnoses']=state['diagnoses']
    return redact(payload)

def initial_state(config):
    return dict(current_body=config['initial_body'],status=config['initial_status'],facts=config['initial_facts'],
        diagnoses=[],completed_calls=0,current_measurement=config['initial_measurement'],
        best_measurement=config['original_candidate']['measurement'] if config['family']=='P_A' else None)

def update_state(config,state,candidate,best):
    state=dict(state)
    state.update(current_body=candidate['body'],status=candidate['verification']['status'],facts=candidate['facts'],
        current_measurement=candidate['measurement'],completed_calls=candidate['call'],
        diagnoses=state['diagnoses']+[candidate['diagnosis']],best_measurement=best['measurement'] if best else None)
    return state

def history_path(family,p,condition,repeat,error=None):
    return run_dir()/'runs'/family/f'P{p}'/(error or 'normal')/condition/f'repeat_{repeat}'

def execute(family,p,condition,repeat,error=None):
    dest=history_path(family,p,condition,repeat,error);dest.mkdir(parents=True,exist_ok=True)
    with (dest/'execution.lock').open('a') as lock:
        try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:return dict(already_running=True)
        if (dest/'result.json').exists():return read(dest/'result.json')
        if not (run_dir()/'egress_approval.json').exists():raise RuntimeError('missing recorded transfer authorization')
        t=task(p,'main' if family=='P_A' else error)
        calibration=read(run_dir()/'calibration'/f'P{p}.json');baseline=calibration['baseline_metrics']
        initial=calibration['verification'] if family=='P_A' else read(run_dir()/'V_A'/f'P{p}'/f'{error}.json')['A3_result']
        if family=='V_B' and initial['status']!=error:raise ValueError(f'P{p} {error}: fixture actually {initial["status"]}')
        cap=1 if family=='P_A' and condition=='A0' else 3 if family=='P_A' else 4
        original=task(p).initial_body
        original_candidate=dict(call=0,origin='original',body=original,proof_sha256=sha(original),eligible=True,
            verification=calibration['verification'],measurement=metrics(calibration['verification'],baseline),facts=facts(calibration['verification']),diagnosis=None)
        config=dict(family=family,problem=p,condition=condition,repeat=repeat,error_category=error,max_calls=cap,
            target=t.config['target'],prefix=t.text[:t.body_start],suffix=t.text[t.body_end:],original_body=original if family=='P_A' else None,
            initial_body=t.initial_body,initial_status=initial['status'],initial_facts=facts(initial),baseline_metrics=baseline,
            initial_measurement=metrics(initial,baseline),original_candidate=original_candidate if family=='P_A' else None)
        # For V, the evaluator's original proof never enters the outbound formatter.
        if (dest/'config.json').exists():
            if read(dest/'config.json')!=config:raise RuntimeError('history configuration changed; do not silently resume')
        else:write(dest/'config.json',config)
        trace,runner,v=backend(dest/'validation',t)
        v.environment=calibration['environment'];v.environment_id=calibration['environment_id']
        if v._environment()!=v.environment:raise RuntimeError('environment changed since calibration')
        write(dest/'run_manifest.json',dict(config_sha256=sha(json.dumps(config,sort_keys=True)),environment_id=v.environment_id,
            original_package_hashes=package_hashes(),adapter_hashes={f.name:sha(f.read_bytes()) for f in HERE.glob('*.py')},
            started_at=time.time(),subscription_only=True))
        budget=Budget.__new__(Budget) if (dest/'model_ledger.json').exists() else Budget(dest/'model_ledger.json',cap)
        if (dest/'model_ledger.json').exists():
            ledger=read(dest/'model_ledger.json');s=ledger['snapshot']
            budget.path=dest/'model_ledger.json';budget.calls=s['calls'];budget.tokens=s['tokens'];budget.max_calls=cap
            budget.max_tokens=s['max_model_tokens'];budget.uncertain=s['accounting_uncertain'];budget.entries=ledger['entries'];budget.quota=s.get('quota')
        state=initial_state(config);candidates=[original_candidate] if family=='P_A' else []
        best=choose(candidates);seen=Counter();events=dest/'events.jsonl'
        if not events.exists():append(events,dict(event='initialized',at=time.time(),config_sha256=sha(json.dumps(config,sort_keys=True))))
        for saved in sorted((dest/'candidates').glob('*/candidate.json')):
            candidate=read(saved);candidates.append(candidate);seen[candidate['proof_sha256']]+=1
            best=choose(candidates);state=update_state(config,state,candidate,best)
        model=CodexModel(runner);stop=None;final=None
        for index in range(state['completed_calls']+1,cap+1):
            if runner.remaining<1:stop='wall_time_limit';break
            if any(n>=2 for n in seen.values()):stop='repeated_candidate';break
            request=make_request(config,state);modeldir=dest/'model_calls'/f'{index:02d}'
            if (modeldir/'request.json').exists() and read(modeldir/'request.json')!=request:raise RuntimeError('resume request differs from recorded bytes')
            if not modeldir.exists():append(events,dict(event='request',call=index,at=time.time(),payload=request,payload_sha256=sha(json.dumps(request,ensure_ascii=False))))
            try:
                if modeldir.exists():
                    if budget.uncertain or not (modeldir/'response.json').exists():raise ModelError('interrupted_call_unknown_usage_or_output')
                    proposal=read(modeldir/'response.json')
                else:proposal=model.propose(request,modeldir,min(300,runner.remaining),budget)
            except ModelError as exc:
                stop=str(exc);append(events,dict(event='model_error',call=index,at=time.time(),reason=stop,budget=budget.snapshot()));break
            body=proposal['proof_body'];proof_sha=sha(body)
            append(events,dict(event='model_response',call=index,at=time.time(),response=proposal,budget=budget.snapshot()))
            cdir=dest/'candidates'/f'{index:02d}';cdir.mkdir(parents=True,exist_ok=True)
            (cdir/'proof.lean').write_text(body);(cdir/'candidate.lean').write_text(t.assemble(body))
            duplicate=next((c for c in candidates if c['proof_sha256']==proof_sha),None)
            if duplicate:
                result=duplicate['verification'];cfacts=duplicate['facts'];cache=True
            else:
                verification=v.verify(body,f'candidate_{index:02d}')
                result=verification.to_dict();cfacts=facts(result);cache=False
            candidate=dict(call=index,origin='generated',body=body,proof_sha256=proof_sha,
                full_source_sha256=sha(t.assemble(body)),eligible=result['status'] in ('candidate_pass','verified'),
                verification=result,measurement=metrics(result,baseline),facts=cfacts,diagnosis=proposal['diagnosis'],
                duplicate_cache=cache,available_at=time.time(),cumulative_calls=budget.calls,cumulative_tokens=budget.tokens,api_spend_usd=None)
            candidates.append(candidate);seen[proof_sha]+=1;best=choose(candidates)
            state=update_state(config,state,candidate,best)
            write(cdir/'candidate.json',candidate)
            append(events,dict(event='candidate',at=candidate['available_at'],candidate=candidate,
                best_sha256=best['proof_sha256'] if best else None,state=state,budget=budget.snapshot()))
            log('candidate',family=family,problem=p,condition=condition,repeat=repeat,error=error,call=index,status=result['status'],tokens=budget.tokens)
            if result['status'] in INFRA:stop=result['status'];break
            if family=='V_B' and candidate['eligible']:
                checked=v.verify(body,f'final_{index:02d}','final');write(cdir/'final_verification.json',checked.to_dict())
                append(events,dict(event='final_verification',at=time.time(),proof_sha256=proof_sha,result=checked.to_dict()))
                if checked.status=='verified':final=checked.to_dict();stop='verified';best=candidate;break
                # Final failures are feedback to the next repair proposal, within the same budget.
                candidate['eligible']=False;candidate['verification']=checked.to_dict();candidate['facts']=facts(checked.to_dict())
                write(cdir/'candidate.json',candidate);best=choose(candidates);state=update_state(config,state,candidate,best)
        if stop is None:stop='one_shot_complete' if family=='P_A' and condition=='A0' else 'search_call_limit' if family=='P_A' else 'repair_limit'
        if family=='P_A':
            # Freeze the order using base measurements only. No holdout result exists here.
            ordered=sorted([c for c in candidates if c['eligible']],key=rank)
            write(dest/'selection_freeze.json',dict(at=time.time(),ranked_hashes=[c['proof_sha256'] for c in ordered],
                selected_sha256=best['proof_sha256'] if best else None,mode='H',holdout_used=False))
            append(events,dict(event='selection_freeze',at=time.time(),ranked_hashes=[c['proof_sha256'] for c in ordered]))
            for n,c in enumerate(ordered):
                checked=v.verify(c['body'],f'selected_final_{n}','final')
                append(events,dict(event='final_verification',at=time.time(),proof_sha256=c['proof_sha256'],result=checked.to_dict()))
                if checked.status=='verified':best=c;final=checked.to_dict();break
            else:best=None
        if best and final and final['status']=='verified':
            (dest/'selected.proof.lean').write_text(best['body']);(dest/'selected.lean').write_text(t.assemble(best['body']))
        value=dict(family=family,problem=p,condition=condition,repeat=repeat,error_category=error,stop_reason=stop,
            verified=bool(final and final['status']=='verified'),selected_sha256=best['proof_sha256'] if best and final else None,
            selected_origin=best['origin'] if best and final else None,selected_measurement=best['measurement'] if best and final else None,
            generated_count=len(candidates)-(1 if family=='P_A' else 0),eligible_generated_count=sum(c['eligible'] and c['origin']=='generated' for c in candidates),
            budget=budget.snapshot(),final_verification=final,candidate_hashes=[c['proof_sha256'] for c in candidates],
            environment_id=v.environment_id,finished_at=time.time(),holdout_used_for_main_selection=False)
        append(events,dict(event='terminal',at=time.time(),result=value));write(dest/'result.json',value)
        append(run_dir()/'measurements.jsonl',value);log('history_complete',family=family,problem=p,condition=condition,repeat=repeat,error=error,
            verified=value['verified'],origin=value['selected_origin'],stop=stop,calls=budget.calls)
        return value

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('family',choices=['P_A','V_B']);parser.add_argument('problem',type=int);parser.add_argument('condition');parser.add_argument('repeat',type=int);parser.add_argument('--error',choices=['proof_error','incomplete'])
    args=parser.parse_args();execute(args.family,args.problem,args.condition,args.repeat,args.error)
