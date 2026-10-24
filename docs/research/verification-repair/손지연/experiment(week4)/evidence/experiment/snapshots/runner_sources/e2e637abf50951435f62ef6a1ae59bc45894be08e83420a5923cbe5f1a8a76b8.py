"""V-C controls; distinguish real Lean evidence from synthetic policy checks."""
from collections import Counter
from copy import deepcopy
import json
from common import read,write,sha,run_dir,log
from tasks import task,backend
from engine import choose,metrics,repetition_limit
from subscription import Budget

def main():
    output=[];root=run_dir()/'controls';root.mkdir(exist_ok=True)
    for variant in ('direct_sorry','indirect_sorry','changed_statement'):
        items=[]
        for p in range(1,16):
            source=run_dir()/'V_A'/f'P{p}'/f'{variant}.json'
            if source.exists():
                result=read(source);items.append(dict(problem=p,passed=result['A3']=='reject',
                    actual_status=result['actual_status'],source=str(source)))
        output.append(dict(control=variant,method='reuse actual V-A Lean/statement-preservation checks',
            scope=len(items),passed=bool(items) and all(x['passed'] for x in items),items=items,additional_model_calls=0,additional_lean_calls=0))
    cal=read(run_dir()/'calibration/P1.json');t=task(1)
    baseline=dict(proof_sha256=sha(t.initial_body),eligible=True,measurement=metrics(cal['verification'],cal['baseline_metrics']))
    valid=dict(proof_sha256='1'*64,eligible=True,measurement=dict(search_score=10,proof_tokens=250,raw_heartbeats=4000000))
    invalid=dict(proof_sha256='2'*64,eligible=False,measurement=dict(search_score=99,proof_tokens=1,raw_heartbeats=1))
    best=choose([baseline,valid,invalid])
    output.append(dict(control='valid_then_invalid',method='synthetic measurements through production best selector',scope=1,
        passed=best['proof_sha256']==valid['proof_sha256'],additional_model_calls=0,additional_lean_calls=0))
    seen=Counter();seen['bad']=1;before=repetition_limit(seen);seen['bad']+=1;after=repetition_limit(seen)
    output.append(dict(control='repeated_candidate',method='production repeated-hash stop predicate with controlled sequence',scope=1,
        passed=not before and after,additional_model_calls=0,additional_lean_calls=0))
    budget=Budget(root/'boundary_ledger.json',max_calls=3) if not (root/'boundary_ledger.json').exists() else Budget.__new__(Budget)
    budget.calls=2;budget.max_calls=3;budget.tokens=220000;budget.max_tokens=240000;budget.uncertain=False
    boundary=budget.can_reserve(20000);overflow=budget.can_reserve(20001)
    budget.calls=3;call_boundary=budget.can_reserve(1)
    output.append(dict(control='reservation_boundary',method='production reservation predicate; exact token edge, one-token overflow, call cap',scope=3,
        passed=boundary and not overflow and not call_boundary,best_preserved=choose([baseline,valid])==valid,
        additional_model_calls=0,additional_lean_calls=0))
    # Actual Lean startup is included in the wall timeout; this is not a solver-hardness benchmark.
    saved=root/'real_timeout.json'
    if saved.exists():timeout=read(saved)
    else:
        trace,runner,v=backend(root/'real_timeout',t);v.task.limits['lean_seconds']=0.05
        _,proc,_,_=v._run(t.assemble(t.initial_body),'forced_deadline')
        timeout=dict(process=proc,actual_status=v._process_status(proc),source_sha256=sha(t.text));write(saved,timeout)
    output.append(dict(control='real_process_timeout',method='actual pinned Lean subprocess; 50ms deadline including startup',scope=1,
        passed=timeout['actual_status']=='timeout',evidence=str(saved),additional_model_calls=0,additional_lean_calls=1))
    saved=root/'environment_failure.json'
    if saved.exists():env=read(saved)
    else:
        broken=task(1);broken.config=deepcopy(broken.config);broken.config['pins']['toolchain']='leanprover/lean4:wrong-experiment-pin'
        trace,runner,v=backend(root/'environment_failure',broken);env=v.prepare().to_dict();write(saved,env)
    output.append(dict(control='environment_failure',method='actual environment pin check; deliberately wrong toolchain pin, no model call',scope=1,
        passed=env['status']=='environment_error',evidence=str(saved),additional_model_calls=0,additional_lean_calls=0))
    # JSON/schema gate behavior is exercised independently; not a provider-error-rate measurement.
    malformed=['not-json','{"diagnosis":"x"}','{"diagnosis":3,"proof_body":"by trivial"}']
    rejected=[]
    for raw in malformed:
        try:
            value=json.loads(raw)
            if set(value)!={'diagnosis','proof_body'} or not all(isinstance(x,str) for x in value.values()):raise ValueError()
            rejected.append(False)
        except (ValueError,TypeError):rejected.append(True)
    output.append(dict(control='malformed_model_output',method='controlled malformed JSON/schema records; no actual provider failure injected',scope=3,
        passed=all(rejected),additional_model_calls=0,additional_lean_calls=0))
    value=dict(checks=output,passed=sum(item['passed'] for item in output),complete_scope=all(item.get('scope')==15 for item in output[:3]),
        caveat='Policy controls isolate production selectors/budget predicates. Only timeout/environment checks and referenced V-A cases execute actual backend behavior; these controls do not measure provider error rates.')
    write(run_dir()/'analysis/control_checks.json',value);log('controls',passed=value['passed'],checks=len(output),complete_scope=value['complete_scope'])

if __name__=='__main__':main()
