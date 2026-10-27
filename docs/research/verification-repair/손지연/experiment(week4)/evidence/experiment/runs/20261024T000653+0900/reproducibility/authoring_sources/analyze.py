"""P-B/P-C and descriptive P/V summaries; USD/official metrics stay null."""
from collections import Counter,defaultdict
from functools import lru_cache
import csv
import html
from itertools import combinations
import json
from pathlib import Path
import statistics
from common import HERE,read,write,run_dir,sha,log,rows as dataset_rows
from prepare import inventory
from engine import rank
from tasks import task

ENVIRONMENTS=list(inventory().values())

def average(values):
    values=[v for v in values if v is not None]
    return statistics.mean(values) if values else None

def descriptive(values):
    values=[v for v in values if v is not None]
    return dict(n=len(values),mean=average(values),median=statistics.median(values) if values else None,
        min=min(values) if values else None,max=max(values) if values else None)

def accounting(values):
    known=sum(r['budget']['tokens'] for r in values)
    complete=all(not r['budget']['accounting_uncertain'] for r in values)
    return dict(model_tokens=known if complete else None,known_model_tokens=known,model_usage_complete=complete)

@lru_cache(maxsize=None)
def compatibility(p,h):
    designated=[e['id'] for e in ENVIRONMENTS if p in e['problems']]
    results=[]
    for env in designated:
        path=run_dir()/'compatibility'/f'P{p}'/h/f'{env}.json'
        results.append(read(path) if path.exists() else dict(environment=env,passed=None,infrastructure_failure=True,pending=True))
    complete=all(r['passed'] is not None and not r['infrastructure_failure'] for r in results)
    k=sum(r['passed'] is True for r in results);m=len(results)
    return dict(k=k,m=m,complete=complete,pct=100*k/m if complete else None,results=results)

def annotate(p,c):
    c=dict(c);comp=compatibility(p,c['proof_sha256']);m=dict(c['measurement'])
    m.update(compatibility=comp['pct'],compatibility_k=comp['k'],compatibility_m=comp['m'],compatibility_complete=comp['complete'])
    m['local_score']=(m['token_reduction_pct']+m['heartbeat_reduction_pct']+comp['pct'])/3 if comp['pct'] is not None else None
    c['measurement']=m;return c

def csv_write(path,values):
    if not values:return
    path.parent.mkdir(parents=True,exist_ok=True)
    keys=list(dict.fromkeys(k for value in values for k in value))
    with path.open('w',newline='') as stream:
        writer=csv.DictWriter(stream,keys);writer.writeheader()
        for value in values:writer.writerow({k:json.dumps(v,ensure_ascii=False) if isinstance(v,(dict,list)) else v for k,v in value.items()})

def main():
    run=run_dir();histories=[];selection=[];curves=[];candidate_rows=[];usd=[]
    for path in sorted((run/'runs').glob('*/*/*/*/*/result.json')):
        r=read(path);r['path']=str(path.parent)
        saved_candidates=[read(f) for f in sorted((path.parent/'candidates').glob('*/candidate.json'))]
        r['candidate_status_distribution']=dict(Counter(c['verification']['status'] for c in saved_candidates))
        r['invalid_candidate_occurrences']=sum(c['verification']['status'] in ('invalid_candidate','statement_mismatch') for c in saved_candidates)
        ledger_path=path.parent/'model_ledger.json'
        entries=read(ledger_path)['entries'] if ledger_path.exists() else []
        r['known_input_tokens']=sum((e.get('usage') or {}).get('input_tokens',0) for e in entries)
        r['known_output_tokens']=sum((e.get('usage') or {}).get('output_tokens',0) for e in entries)
        r['unknown_usage_calls']=sum(e['state']=='unknown_usage' for e in entries)
        # Read the local evaluator's reference; it never enters a V-B request.
        r['restored_original_exact']=bool(r['verified'] and r['selected_sha256']==sha(task(r['problem']).initial_body))
        histories.append(r)
        if r['family']!='P_A':continue
        config=read(path.parent/'config.json');p=r['problem']
        candidates=[config['original_candidate']]+[read(f) for f in sorted((path.parent/'candidates').glob('*/candidate.json'))]
        eligible={}
        for c in candidates:
            if c['eligible']:eligible.setdefault(c['proof_sha256'],annotate(p,c))
        for c in eligible.values():candidate_rows.append(dict(history=str(path.parent),problem=p,condition=r['condition'],repeat=r['repeat'],proof_sha256=c['proof_sha256'],origin=c['origin'],**c['measurement']))
        selected=eligible.get(r['selected_sha256'])
        if selected:r['posthoc_measurement']=selected['measurement']
        for policy in ('min_tokens','min_heartbeats','max_compatibility','max_local_score'):
            values=list(eligible.values());available=bool(values)
            if policy in ('max_compatibility','max_local_score') and any(c['measurement']['compatibility'] is None for c in values):available=False
            if available:
                def key(c):
                    m=c['measurement'];primary=m['proof_tokens'] if policy=='min_tokens' else m['raw_heartbeats'] if policy=='min_heartbeats' else -m['compatibility'] if policy=='max_compatibility' else -m['local_score']
                    return primary,m['proof_tokens'],m['raw_heartbeats'],c['proof_sha256']
                picked=min(values,key=key)
            else:picked=None
            selection.append(dict(history=str(path.parent),problem=p,condition=r['condition'],repeat=r['repeat'],policy=policy,
                candidate_count=len(values),selected_sha256=picked['proof_sha256'] if picked else None,
                selected_origin=picked['origin'] if picked else None,measurement=picked['measurement'] if picked else None,
                available=available,posthoc=True,main_selection_replaced=False))
        best=config['original_candidate'];calls=0;tokens=0
        curves.append(dict(history=str(path.parent),problem=p,condition=r['condition'],repeat=r['repeat'],calls=0,model_tokens=0,
            best_sha256=best['proof_sha256'],search_score=0,availability='baseline',api_spend_usd=None))
        for line in (path.parent/'events.jsonl').read_text().splitlines():
            event=json.loads(line)
            if event['event']=='model_response':
                b=event['budget'];last=curves[-1]
                curves.append(dict(history=str(path.parent),problem=p,condition=r['condition'],repeat=r['repeat'],calls=b['calls'],model_tokens=b['tokens'],
                    best_sha256=last['best_sha256'],search_score=last['search_score'],available_at=event['at'],availability='model_output_not_yet_validated',api_spend_usd=None))
            elif event['event']=='candidate':
                b=event['budget'];h=event['best_sha256'];m=event['state']['best_measurement']
                curves.append(dict(history=str(path.parent),problem=p,condition=r['condition'],repeat=r['repeat'],calls=b['calls'],model_tokens=b['tokens'],
                    best_sha256=h,search_score=m['search_score'] if m else None,available_at=event['at'],availability='validation_completed',api_spend_usd=None))
            elif event['event']=='model_error':
                b=event['budget'];last=curves[-1]
                curves.append(dict(history=str(path.parent),problem=p,condition=r['condition'],repeat=r['repeat'],calls=b['calls'],model_tokens=b['tokens'],
                    best_sha256=last['best_sha256'],search_score=last['search_score'],available_at=event['at'],availability='no_new_candidate_model_error',api_spend_usd=None))
        curves.append(dict(history=str(path.parent),problem=p,condition=r['condition'],repeat=r['repeat'],calls=r['budget']['calls'],model_tokens=r['budget']['tokens'],
            best_sha256=r['selected_sha256'],search_score=(r.get('selected_measurement') or {}).get('search_score') if r['verified'] else None,
            available_at=r['finished_at'],availability='frozen_final_selection',api_spend_usd=None))
        for checkpoint in (0.5,1.0,2.0,3.0):usd.append(dict(history=str(path.parent),usd_checkpoint=checkpoint,selected_sha256=None,score=None,
            status='not_measurable_subscription',reason='No actual per-call USD invoice; no API price conversion or fabricated zero.'))
    pvalues=[r for r in histories if r['family']=='P_A'];vvalues=[r for r in histories if r['family']=='V_B']
    for point in curves:
        comp=compatibility(point['problem'],point['best_sha256']) if point['best_sha256'] else None
        c=comp['pct'] if comp else None
        point['posthoc_compatibility']=c
        point['posthoc_local_score']=(2*point['search_score']+c)/3 if point['search_score'] is not None and c is not None else None
        point['holdout_was_available_during_search']=False
    summary=[]
    for condition in ('A0','A1','A2','A3'):
        values=[r for r in pvalues if r['condition']==condition];measure=[r.get('posthoc_measurement') or {} for r in values]
        summary.append(dict(condition=condition,completed=len(values),planned=45,verified=sum(r['verified'] for r in values),
            selected_generated=sum(r['selected_origin']=='generated' for r in values),selected_original=sum(r['selected_origin']=='original' for r in values),
            improved=sum((r.get('selected_measurement') or {}).get('search_score',0)>0 for r in values),
            mean_token_reduction=average(m.get('token_reduction_pct') for m in measure),mean_heartbeat_reduction=average(m.get('heartbeat_reduction_pct') for m in measure),
            mean_compatibility=average(m.get('compatibility') for m in measure),mean_local_score=average(m.get('local_score') for m in measure),
            compatibility_measured=sum(m.get('compatibility') is not None for m in measure),model_calls=sum(r['budget']['calls'] for r in values),
            generated_candidates=sum(r['generated_count'] for r in values),
            known_input_tokens=sum(r['known_input_tokens'] for r in values),known_output_tokens=sum(r['known_output_tokens'] for r in values),
            **accounting(values),api_spend_usd=None,score_official=None,stop_reasons=dict(Counter(r['stop_reason'] for r in values))))
    vsummary=[]
    for condition in ('B1','B2'):
        for category in ('proof_error','incomplete'):
            values=[r for r in vvalues if r['condition']==condition and r['error_category']==category]
            vsummary.append(dict(condition=condition,error_category=category,completed=len(values),planned=45,verified=sum(r['verified'] for r in values),
                success_rate=sum(r['verified'] for r in values)/len(values) if values else None,
                mean_success_calls=average(r['budget']['calls'] for r in values if r['verified']),model_calls=sum(r['budget']['calls'] for r in values),
                generated_candidates=sum(r['generated_count'] for r in values),invalid_candidate_occurrences=sum(r['invalid_candidate_occurrences'] for r in values),
                restored_original_exact=sum(r['restored_original_exact'] for r in values),
                verified_different_bytes=sum(r['verified'] and not r['restored_original_exact'] for r in values),
                known_input_tokens=sum(r['known_input_tokens'] for r in values),known_output_tokens=sum(r['known_output_tokens'] for r in values),
                unknown_usage_calls=sum(r['unknown_usage_calls'] for r in values),
                **accounting(values),api_spend_usd=None,stop_reasons=dict(Counter(r['stop_reason'] for r in values))))
    problem_summary=[];variation=[]
    groups=defaultdict(list)
    for r in histories:groups[r['family'],r['problem'],r['condition'],r['error_category']].append(r)
    for (family,p,condition,error),values in sorted(groups.items()):
        m=[r.get('posthoc_measurement') or r.get('selected_measurement') or {} for r in values]
        problem_summary.append(dict(family=family,problem=p,condition=condition,error_category=error,completed=len(values),planned=3,
            designated_environment_count=sum(p in e['problems'] for e in ENVIRONMENTS),
            verified=sum(r['verified'] for r in values),generated_selected=sum(r['selected_origin']=='generated' for r in values),
            mean_token_reduction=average(x.get('token_reduction_pct') for x in m),mean_heartbeat_reduction=average(x.get('heartbeat_reduction_pct') for x in m),
            mean_compatibility=average(x.get('compatibility') for x in m),mean_local_score=average(x.get('local_score') for x in m),
            model_calls=sum(r['budget']['calls'] for r in values),**accounting(values),
            distributions={k:descriptive(x.get(k) for x in m) for k in ('token_reduction_pct','heartbeat_reduction_pct','compatibility','local_score')}))
        first=[]
        for r in values:
            file=Path(r['path'])/'candidates/01/candidate.json'
            first.append(read(file)['proof_sha256'] if file.exists() else None)
        finals=[r['selected_sha256'] for r in values]
        variation.append(dict(family=family,problem=p,condition=condition,error_category=error,repeats=len(values),
            first_candidate_hashes=first,distinct_first_candidates=len({h for h in first if h}),final_hashes=finals,
            distinct_final_proofs=len({h for h in finals if h}),failed_or_missing_final=sum(h is None for h in finals),
            same_successful_final_all_repeats=len(values)==3 and all(finals) and len(set(finals))==1))
    acases=[read(p) for p in sorted((run/'V_A').glob('P*/*.json'))]
    validation=[]
    for judge in ('A1','A2','A3'):
        validation.append(dict(judge=judge,cases=len(acases),planned=90,
            false_accept=sum(not a['expected_valid'] and a[judge]=='accept' for a in acases),false_reject=sum(a['expected_valid'] and a[judge]=='reject' for a in acases),
            abstain=sum(a[judge]=='abstain' for a in acases),not_available=sum(a[judge]=='not_available' for a in acases)))
    # Count live/in-flight ledgers as well, so the total never hides discarded or unfinished calls.
    ledgers=[read(p) for p in (run/'runs').glob('*/*/*/*/*/model_ledger.json')]
    live_tokens=sum(x['snapshot']['tokens'] for x in ledgers);live_calls=sum(x['snapshot']['calls'] for x in ledgers)
    unknown_usage=sum(e['state']=='unknown_usage' for ledger in ledgers for e in ledger['entries'])
    pending_usage=sum(e['state']=='in_flight' for ledger in ledgers for e in ledger['entries'])
    overrun_ledgers=[x['snapshot'] for x in ledgers if x['snapshot']['tokens']>x['snapshot']['max_model_tokens']]
    status=dict(run_id=run.name,baseline_problems=len(list((run/'calibration').glob('P*.json'))),designated_environments=len(ENVIRONMENTS),
        ready_environments=len(list((run/'preparation').glob('*_ready.json'))),designated_problem_environment_pairs=sum(len(e['problems']) for e in ENVIRONMENTS),
        P_A_completed=len(pvalues),P_A_planned=180,V_A_cases=len(acases),V_A_planned=90,V_B_completed=len(vvalues),V_B_planned=180,
        actual_model_calls=live_calls,actual_model_tokens=live_tokens if not unknown_usage and not pending_usage else None,
        known_model_tokens=live_tokens,unknown_usage_calls=unknown_usage,pending_usage_calls=pending_usage,
        soft_token_overrun_histories=len(overrun_ledgers),soft_token_overrun_amount=sum(x['tokens']-x['max_model_tokens'] for x in overrun_ledgers),
        in_flight_or_uncertain_ledgers=sum(x['snapshot']['accounting_uncertain'] for x in ledgers),
        api_spend_usd=None,score_official=None,complete=len(pvalues)==180 and len(vvalues)==180 and len(acases)==90,
        experiments='New 15-problem integrated P/V experiment; previous v0/v1 excluded')
    baseline_comparison=[]
    for p,row in enumerate(dataset_rows(),1):
        source=run/'calibration'/f'P{p}.json'
        if not source.exists():continue
        measured=read(source)['baseline_metrics']
        baseline_comparison.append(dict(problem=p,dataset_proof_length=row.get('proof_length'),local_native_proof_tokens=measured['proof_tokens'],
            token_count_equal=row.get('proof_length')==measured['proof_tokens'],local_raw_heartbeats=measured['raw_heartbeats'],
            local_heartbeat_units=measured['heartbeats'],official_worker_equivalence=False))
    unique_candidates={(r['problem'],r['proof_sha256']) for r in candidate_rows}
    expected_compatibility=sum(sum(p in e['problems'] for e in ENVIRONMENTS) for p,h in unique_candidates)
    attempted_compatibility=sum((run/'compatibility'/f'P{p}'/h/f"{e['id']}.json").exists() for p,h in unique_candidates for e in ENVIRONMENTS if p in e['problems'])
    status['main_complete']=status['complete']
    status['compatibility_checks_expected']=expected_compatibility;status['compatibility_checks_attempted']=attempted_compatibility
    status['completion_manifest_present']=(run/'completion.json').exists()
    status['complete']=bool(status['main_complete'] and status['completion_manifest_present'] and read(run/'completion.json').get('execution_complete'))
    status['model_usage_complete']=not unknown_usage and not pending_usage
    status['soft_token_limits_all_satisfied']=not overrun_ledgers
    status['usd3_strict_compliance']=None
    status['arena_closed_track_compliant']=False
    paired=[]
    for metric in ('mean_token_reduction','mean_heartbeat_reduction','mean_compatibility','mean_local_score'):
        for control in ('A0','A1','A2'):
            differences=[]
            for p in range(1,16):
                left=next((x for x in problem_summary if x['family']=='P_A' and x['problem']==p and x['condition']==control),None)
                right=next((x for x in problem_summary if x['family']=='P_A' and x['problem']==p and x['condition']=='A3'),None)
                if left and right and left[metric] is not None and right[metric] is not None:
                    differences.append(dict(problem=p,difference=right[metric]-left[metric]))
            paired.append(dict(metric=metric,contrast=f'A3 minus {control}',unit='paired problem means over three repeats',
                **descriptive(x['difference'] for x in differences),problems=differences))
    token_checkpoints=[]
    for condition in ('A0','A1','A2','A3'):
        for checkpoint in (40000,80000,160000,240000):
            values=[]
            for h in {c['history'] for c in curves if c['condition']==condition}:
                eligible=[c for c in curves if c['history']==h and c['model_tokens']<=checkpoint]
                if eligible:values.append(eligible[-1]['search_score'])
            token_checkpoints.append(dict(condition=condition,model_token_checkpoint=checkpoint,
                **descriptive(values),unit='available best base search score; stopped histories carry their last available best',
                api_spend_usd=None,extra_model_calls=0))
    example_specs=[('P: generated improvement',lambda r:r['family']=='P_A' and r['selected_origin']=='generated'),
        ('P: original fallback',lambda r:r['family']=='P_A' and r['selected_origin']=='original'),
        ('V: verified repair',lambda r:r['family']=='V_B' and r['verified']),
        ('V: repair limit',lambda r:r['family']=='V_B' and r['stop_reason']=='repair_limit'),
        ('V: Lean timeout',lambda r:r['family']=='V_B' and r['stop_reason']=='timeout'),
        ('V: model timeout and unknown usage',lambda r:r['stop_reason']=='subscription_timeout'),
        ('V: detected soft token overrun',lambda r:r['stop_reason']=='subscription_token_limit')]
    examples=[]
    for label,predicate in example_specs:
        r=next((r for r in histories if predicate(r)),None)
        if r:examples.append(dict(label=label,history=str(Path(r['path']).relative_to(run)),problem=r['problem'],condition=r['condition'],
            repeat=r['repeat'],stop_reason=r['stop_reason'],selected_origin=r['selected_origin'],verified=r['verified'],budget=r['budget']))
    selections_by_history=defaultdict(dict)
    for s in selection:selections_by_history[s['history']][s['policy']]=s
    conflicts=[]
    for left,right in combinations(('min_tokens','min_heartbeats','max_compatibility','max_local_score'),2):
        pairs=[(s[left],s[right]) for s in selections_by_history.values() if s[left]['available'] and s[right]['available']]
        conflicts.append(dict(left=left,right=right,paired_histories=len(pairs),
            identical_candidate=sum(a['selected_sha256']==b['selected_sha256'] for a,b in pairs),
            different_candidate=sum(a['selected_sha256']!=b['selected_sha256'] for a,b in pairs),
            right_minus_left={key:descriptive(b['measurement'][key]-a['measurement'][key] for a,b in pairs
                if a['measurement'][key] is not None and b['measurement'][key] is not None)
                for key in ('token_reduction_pct','heartbeat_reduction_pct','compatibility','local_score')}))
    for name,value in [('status',status),('summary',summary),('feedback_comparison',vsummary),('validation_comparison',validation),
        ('validation_label_mismatches',[a for a in acases if not a['expected_status_match']]),('selection_comparison',selection),('budget_curve',curves),
        ('usd_budget_checkpoints',usd),('candidate_measurements',candidate_rows),('histories',histories),('baseline_comparison',baseline_comparison),
        ('problem_summary',problem_summary),('repeat_variation',variation),('paired_problem_comparison',paired),
        ('token_budget_checkpoints',token_checkpoints),('representative_histories',examples),('policy_conflicts',conflicts)]:
        write(run/'analysis'/f'{name}.json',value)
        if isinstance(value,list):csv_write(run/'analysis'/f'{name}.csv',value)
    lines=['# 실험 진행·결과 보고서','',f'실행: `{run.name}`. 상태: '+('실행·후속 평가 완료' if status['complete'] else '**실행 중 — 최종 결과 아님**')+'.',
        '',f'정상 원본 기준 검증 {status["baseline_problems"]}/15, 환경 {status["ready_environments"]}/15, P-A {len(pvalues)}/180, V-A {len(acases)}/90, V-B {len(vvalues)}/180.',
        '',f'실제 모델 호출 {live_calls}회, 확인된 입출력 token {live_tokens:,}. API USD 비용·공식 점수·USD 3 준수 여부는 측정 불가(null).',
        '',f'최종 usage 미수신 호출 {unknown_usage}회, 진행 중 usage {pending_usage}회. 미수신 사용량을 0으로 가정하지 않으며 총 token은 이들이 해소되기 전까지 null이다. 확인된 합계는 하한이다.',
        '',f'240,000 soft token 상한 초과 이력 {len(overrun_ledgers)}건, 확인된 초과량 합계 {sum(x["tokens"]-x["max_model_tokens"] for x in overrun_ledgers):,} token. 응답 전 예약 추정과 실제 usage의 차이이며 감지 후 추가 호출·후보 채택을 중단했다. 구독 transport의 hard output cap을 보장하지 못한다.',
        '',f'후보/환경 호환성 검사 {attempted_compatibility}/{expected_compatibility}. 이 분모는 완료된 P-A 후보군을 반영하므로 주 실행 중에는 증가한다.',
        '', 'P는 정상 proof를 제공한 리팩터링이다. V는 통제된 proof 오류/미완성 변형을 사용하고 원본 정답 proof를 모델에게 숨겼다. 모든 모델은 기존 GPT 구독 인증으로 호출했다.',
        '', '기준 버전만 사용하는 H 모드다. 선택을 고정한 뒤 지정된 모든 버전에서 동일 proof bytes를 평가한다. P-B의 호환성/종합 점수 선택은 사후 분석이며 실제 선택을 바꾸지 않는다.',
        '', '지정 환경 수는 문제마다 다르다. P1·P2·P4·P5·P6은 1개 환경이므로 이 문제들의 1/1 호환성은 여러 버전의 통과를 뜻하지 않는다. 나머지 문제는 실제 지정된 2~4개 환경을 분모로 사용한다.',
        '', '고정 조건은 [protocol.json](protocol.json), 버전·commit·경로는 [환경 manifest](environment_manifest.json)에 있다. 모델은 gpt-5.6-sol, effort high, 파일·웹·셸 도구 없는 새 이력이다. sampling/seed 및 강제 출력 token 상한은 구독 CLI에서 확보하지 못했다. A0는 1회, A1~A3은 최대 3회, V-B는 최대 4회 호출한다. Lean/모델 프로세스 timeout은 각각 300초, 이력 wall time은 5,400초다.',
        '', '호스트 정보는 [runtime manifest](runtime_manifest.json), 병렬 실행은 [parallelism manifest](parallelism_manifest.json)와 [실행 중 조정 기록](runtime_adjustments.jsonl)에 있다. 같은 호스트에서 여러 이력·검증이 겹쳤으므로 wall timeout/지연을 격리된 성능이나 공급자 오류율로 해석하지 않는다. native heartbeat는 wall time과 별도로 계측했다.',
        '', 'A0는 한 번 제안한다. A1은 원본에서 새 후보를 만들며 실패 진단을 피드백하지 않는다. A2는 현재 후보·원시 진단으로 수리하고 성공 이후에도 탐색한다. A3는 A2에 기준 버전 token/HB·탐색 점수 피드백을 추가한다. 모든 조건이 검증된 원본 fallback을 보존한다.',
        '', '| P-A | 완료/예정 | 생성 선택 | 원본 유지 | 점수 개선 | token 감소 % | HB 감소 % | 호환성 % | 로컬 종합 | 호환성 측정 |',
        '|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
    def fmt(x):return '미측정' if x is None else f'{x:.2f}'
    for s in summary:lines.append(f'| {s["condition"]} | {s["completed"]}/45 | {s["selected_generated"]} | {s["selected_original"]} | {s["improved"]} | {fmt(s["mean_token_reduction"])} | {fmt(s["mean_heartbeat_reduction"])} | {fmt(s["mean_compatibility"])} | {fmt(s["mean_local_score"])} | {s["compatibility_measured"]}/45 |')
    lines+=['','| P-A | 실제 모델 호출 | 저장 제안 후보 | 확인된 input token | 확인된 output token |', '|---|---:|---:|---:|---:|']
    for s in summary:lines.append(f'| {s["condition"]} | {s["model_calls"]} | {s["generated_candidates"]} | {s["known_input_tokens"]:,} | {s["known_output_tokens"]:,} |')
    lines+=['','탐색 점수 개선은 사전 정의한 기준 환경 search_score > 0이다. token과 HB가 모두 감소했다는 뜻은 아니며, 작은 차이는 별도 heartbeat 재계측 변동과 함께 읽어야 한다.',
        '', f'{sum(r["verified"] for r in pvalues)}/{len(pvalues)} 최종 verified에는 원본 fallback {sum(r["selected_origin"]=="original" for r in pvalues)}회가 포함된다. 생성 후보를 선택한 {sum(r["selected_origin"]=="generated" for r in pvalues)}회와 구분해야 한다. 후보 검증 성공을 곧바로 원본보다 개선한 새 증명 수라고 해석하지 않는다.',
        '','| V-A | 검사 | 오수락 | 오거절 | 보류 | 관측 불가 |','|---|---:|---:|---:|---:|---:|']
    for s in validation:lines.append(f'| {s["judge"]} | {s["cases"]} | {s["false_accept"]} | {s["false_reject"]} | {s["abstain"]} | {s["not_available"]} |')
    lines+=['','V-A의 A1은 종료 코드, A2는 종료 코드와 실제 native InfoTree의 바깥 tactic goals_after, A3는 고정 명제·정책·완성 여부·전이 공리를 검사한다. 오수락 종류별 개수는 '+json.dumps({judge:dict(Counter(a['variant'] for a in acases if not a['expected_valid'] and a[judge]=='accept')) for judge in ('A1','A2','A3')},ensure_ascii=False)+'. 이 통제된 fixture 집합에서의 결과이며 일반적 오수락률을 추정한 수치가 아니다.']
    lines+=['','| V-B | 오류 유형 | 완료/예정 | verified | 성공률 | 모델 호출 |','|---|---|---:|---:|---:|---:|']
    for s in vsummary:lines.append(f'| {s["condition"]} | {s["error_category"]} | {s["completed"]}/45 | {s["verified"]} | {fmt(100*s["success_rate"] if s["success_rate"] is not None else None)}% | {s["model_calls"]} |')
    lines+=['','| V-B | 오류 | 성공 이력의 평균 호출 | 무효 후보 발생 | 정상 원본과 같은 proof 복구 | 확인된 input / output token |', '|---|---|---:|---:|---:|---:|']
    for s in vsummary:lines.append(f'| {s["condition"]} | {s["error_category"]} | {fmt(s["mean_success_calls"])} | {s["invalid_candidate_occurrences"]} | {s["restored_original_exact"]} | {s["known_input_tokens"]:,} / {s["known_output_tokens"]:,} |')
    lines+=['','성공 이력 평균 호출의 분모는 위 표의 verified 수다. 정상 원본과의 비교는 proof bytes의 동일성만 뜻하며, 최적화 지표는 P 실험에 별도로 기록했다.']
    for s in vsummary:
        if s['unknown_usage_calls']:lines+=['',f'{s["condition"]} {s["error_category"]}에는 usage 미수신 호출 {s["unknown_usage_calls"]}건이 있어 확인된 token 합계는 하한이다.']
    lines+=['','V-B 전체 종료 분포: '+json.dumps(dict(Counter(r['stop_reason'] for r in vvalues)),ensure_ascii=False)+f'. 성공 이력만 남기지 않고 완료된 {len(vvalues)}개 이력의 비용·중단 사유를 집계했다.']
    lines+=['','V-B의 B1은 같은 진단·goal·local context 사실을 원시 텍스트로 제공하고, B2는 구조화된 상태·사실과 상태별 지침을 제공한다. 비교는 status 라벨 하나의 효과가 아니라 진단 표현·지침·이어진 이력 및 프롬프트 비용을 포함한다. B2−B1 복구 횟수 차이는 '+json.dumps({category:sum(r['verified'] for r in vvalues if r['condition']=='B2' and r['error_category']==category)-sum(r['verified'] for r in vvalues if r['condition']=='B1' and r['error_category']==category) for category in ('proof_error','incomplete')})+'. P의 정상 proof 리팩터링 성과와 V의 손상 proof 복구율은 같은 성공 지표로 합치지 않는다.']
    lines+=['','P-B는 같은 이력의 유효 후보와 원본 fallback에 네 선택 정책을 적용한 사후 비교다. B4가 같은 종합 점수에서 최대인 것은 선택 정의의 결과이며 생성 능력의 우월성 근거가 아니다.',
        '', '| P-B 정책 | 선택 가능 이력 | C·점수 측정 이력 | token 감소 평균 % | HB 감소 평균 % | 호환성 평균 % | 로컬 종합 평균 |',
        '|---|---:|---:|---:|---:|---:|---:|']
    for policy in ('min_tokens','min_heartbeats','max_compatibility','max_local_score'):
        values=[s['measurement'] for s in selection if s['policy']==policy and s['available']]
        measured=sum(v['compatibility'] is not None for v in values)
        lines.append('| '+policy+' | '+str(len(values))+' | '+str(measured)+' | '+' | '.join(fmt(average(v.get(k) for v in values)) for k in ('token_reduction_pct','heartbeat_reduction_pct','compatibility','local_score'))+' |')
    conflict=next(x for x in conflicts if x['left']=='min_tokens' and x['right']=='min_heartbeats')
    lines+=['',f'token 최소와 HB 최소는 분석 가능한 {conflict["paired_histories"]}개 이력 중 {conflict["different_candidate"]}개에서 서로 다른 후보를 골랐다. 정책별 동일 후보 선택 수와 단일 지표 선택에 따른 점수 차이는 [정책 충돌 분석](analysis/policy_conflicts.json)에 있다.']
    lines+=['','P-C의 USD 0.50/1/2/3 체크포인트는 [USD 분석](analysis/usd_budget_checkpoints.json)에 모두 null로 보존했다. 아래는 별도 보조축인 실제 누적 model token 기준이며 달러 예산 동등 비교를 뜻하지 않는다. 모델 응답이 도착한 시점과 Lean 검증이 끝나 후보가 이용 가능해진 시점을 구분했다. 조기 종료 이력은 마지막 best를 유지한다.',
        '', '| 조건 | 40k token | 80k token | 160k token | 240k token |', '|---|---:|---:|---:|---:|']
    for condition in ('A0','A1','A2','A3'):
        values=[x for x in token_checkpoints if x['condition']==condition]
        lines.append('| '+condition+' | '+' | '.join(fmt(x['mean']) for x in values)+' |')
    lines+=['','[문제별 평균·중앙값·범위](analysis/problem_summary.json), [문제 내 평균의 대응 차이](analysis/paired_problem_comparison.json), [독립 반복의 코드 해시 분산](analysis/repeat_variation.json)을 별도로 보존했다. 전역 평균은 모든 3회 반복이 있는 조건의 기술통계이며, 호환성 미측정 값은 평균 분모에서 제외하고 측정 이력 수를 함께 표시한다.',
        '', 'A0는 한 번만 호출하므로 다른 조건보다 실제 소비량이 작다. 구독 실행은 USD 3 동등 비용·공식 대회 규칙 준수 실험으로 해석할 수 없다.']
    measured_summary=[s for s in summary if s['mean_token_reduction'] is not None and s['mean_heartbeat_reduction'] is not None]
    if measured_summary:
        best_condition=max(measured_summary,key=lambda s:s['mean_token_reduction']+s['mean_heartbeat_reduction'])['condition']
        lines+=['',f'이 실행의 원본 fallback 포함 기준 버전 token/HB 평균 감소 합은 {best_condition}에서 가장 컸다. 점수 피드백의 추가가 항상 더 좋은 후보를 만든다고 결론 내리지 않는다.']
    replay_path=run/'analysis/record_replay.json'
    lines+=['','새 모델 독립 반복과 기록 재생·새 Lean 실행은 서로 다른 결과다. 새 생성의 코드 일치 관측은 다음과 같다.',
        '', '| 새 생성 반복 | 문제·조건 그룹 | 3회 최종 proof가 모두 같은 성공 그룹 | 첫 후보 3개가 모두 다른 그룹 |', '|---|---:|---:|---:|']
    for family in ('P_A','V_B'):
        values=[v for v in variation if v['family']==family]
        lines.append(f'| {family} | {len(values)} | {sum(v["same_successful_final_all_repeats"] for v in values)} | {sum(v["distinct_first_candidates"]==3 for v in values)} |')
    lines+=['','P의 같은 최종 proof에는 원본 fallback도 포함된다. 같은 선택 결과나 높은 재생 일치율은 모델 생성의 결정성을 보장하지 않는다.']
    if replay_path.exists():
        r=read(replay_path);lines+=['',f'V-C 기록 재생: {r["matched"]}/{r["histories"]} 이력 일치. 추가 모델 0회, Lean 0회.']
    revalidation_path=run/'analysis/lean_revalidation.json'
    if revalidation_path.exists():
        r=read(revalidation_path);lines+=['',f'V-C 실제 Lean 재검증: {r["semantic_matches"]}/{r["unique_candidate_environment_checks"]} 판정·해시·환경 및 관측된 공리 비교 일치. 항목별 일치 수: '+json.dumps(r['field_matches'],ensure_ascii=False)+'.']
        lines+=['',f'재검증 단위는 문제·proof SHA·환경·check_kind다. 같은 proof의 candidate/final 판정은 별도 비교하며, check_kind를 합친 문제·proof·환경 조합은 {r["unique_problem_proof_environment_pairs"]}개다. 이를 새 모델 독립 실행 수에 더하지 않는다.']
        if 'field_comparisons' in r:lines+=['','위 항목별 비교 가능 분모: '+json.dumps(r['field_comparisons'],ensure_ascii=False)+'. 한쪽이라도 미측정인 token/HB/공리는 값 비교에서 제외한다.']
        if 'field_availability_changes' in r:lines+=['','미측정 ↔ 관측으로 바뀐 항목 수: '+json.dumps(r['field_availability_changes'],ensure_ascii=False)+'. 관측 유무의 변화와 실제 측정값 차이는 분리했다.']
        if 'heartbeat_remeasurement_pct' in r:lines+=['','HB 재계측 상대 변화(%): '+json.dumps(r['heartbeat_remeasurement_pct'],ensure_ascii=False)+'. 진단 원문에는 임시 파일 경로 차이가 있어 원문 완전 일치와 메시지 내용 일치를 따로 비교한다.']
        difference_file=run/'analysis/revalidation_differences.json'
        if difference_file.exists():
            differences=read(difference_file)
            lines+=['','판정·공리·메시지·token 등 항목별 불일치 근거는 [재검증 차이 목록](analysis/revalidation_differences.json)에 있다. 원래 판정·계측을 새 값으로 덮어쓰지 않았다.']
            for field in ('status','diagnostic_messages'):
                if differences[field]:
                    first=differences[field][0]
                    lines+=['',f'{field} 불일치 {len(differences[field])}건. 첫 사례: P{first["problem"]} / {first["environment"]}, {first["old_status"]} → {first["actual_status"]} ([원문 비교]({first["comparison_file"]})).']
            recovered=[x for x in differences['status'] if x['old_status']=='timeout' and x['actual_status']=='verified']
            if recovered:lines+=['',f'timeout → verified 관측 {len(recovered)}건은 자원·시간 판정의 불일치다. 같은 proof와 환경 해시는 보존됐으며, 최초 호환성·주 점수의 미확정 기록은 유지한다. 뒤의 성공을 최초 실행 결과로 소급하지 않았다.']
    control_path=run/'analysis/control_checks.json'
    if control_path.exists():
        c=read(control_path);lines+=['',f'V-C 대조: {c["passed"]}/{len(c["checks"])} 경로 통과. 15문제 전체 V-A fixture 참조 완료 여부: {c["complete_scope"]}. 실제 timeout·환경 검사와 synthetic 모델/정책 검사를 구분했다.']
    audit_path=run/'analysis/audit.json'
    if audit_path.exists():
        a=read(audit_path);lines+=['',f'완료된 실제 Lean subprocess 기록은 {a["verification_lean_process_records"]:,}건이다. 한 후보 검증은 guard·컴파일·계측·InfoTree/공리 검사 등 여러 subprocess를 사용할 수 있어 후보 수와 다르다. 의존성 build/cache와 진행 중 프로세스는 이 수에 넣지 않는다. 영역별 수: '+json.dumps(a.get('verification_lean_process_records_by_area',{}))+'.',
            '',f'감사: ledger 사용량 산술 불일치 {len(a["accounting_mismatches"])}건, 모델 도구 사용 {len(a["tool_events"])}건, 요청의 로컬 절대 경로 노출 {len(a["redaction_failures"])}건, 중복 thread {len(a["duplicate_threads"])}건. 원본 재사용 패키지 불변: {a["original_package_unchanged"]}. 미수신 usage와 soft 상한 초과는 이 무결성 검사 통과와 별개다.']
        if 'v_feedback_input_pairs_checked' in a:lines+=['',f'실제 첫 입력 {a["initial_model_inputs_checked"]}건의 원본/손상 source 구성 불일치 {len(a["initial_model_input_mismatches"])}건. V-B의 같은 문제·오류·반복에 해당하는 B1/B2 {a["v_feedback_input_pairs_checked"]}쌍에서 초기 손상 proof·문맥·진단 사실·상한 불일치 {len(a["v_feedback_input_pair_mismatches"])}건.']
    lines+=['','대표 실행은 성공·원본 유지·실패·자원 중단을 함께 추적할 수 있도록 골랐다. 각 링크의 events.jsonl, model_calls/, candidates/, result.json이 원문 근거다.',
        '', '| 사례 | 문제·조건·반복 | 종료 | 선택 | 기록 |', '|---|---|---|---|---|']
    for e in examples:lines.append(f'| {e["label"]} | P{e["problem"]} / {e["condition"]} / {e["repeat"]} | {e["stop_reason"]} | {e["selected_origin"]} | [result]({e["history"]}/result.json) · [events]({e["history"]}/events.jsonl) |')
    if (run/'analysis/candidate_lineage.json').exists():lines+=['','[후보 계보와 proof diff](analysis/candidate_lineage.json)는 실제 전송 요청의 입력 proof와 대조해 사후 생성했다. A0/A1은 매번 정상 원본을 부모로, A2/A3/V-B는 실제 직전 입력 후보를 부모로 기록한다. 원래 요청·응답·판정 기록은 변경하지 않았다.']
    lines+=['','직접 sorry는 패키지의 엄격 guard가 `invalid_candidate(policy)`로 거절할 수 있다. DESIGN의 기대 상태 `incomplete`와의 라벨 차이는 별도 파일에 기록하며, 이를 오수락과 혼동하지 않는다.',
        '', '15문제의 작은 개발 표본에 대한 기술통계다. 문제별 결과와 독립 반복을 보존하며, 정책·반복 간 후보를 하나의 예산 실행처럼 합치지 않는다.',
        '', '원시 기록: `runs/`, `baseline/`, `V_A/`, `compatibility/`. [요약](analysis/summary.json), [선택 비교](analysis/selection_comparison.json), [이용 가능 시점별 곡선](analysis/budget_curve.json), [재생](analysis/record_replay.json), [새 Lean 재검증](analysis/lean_revalidation.json), [감사](analysis/audit.json). 재실행·재개 명령과 구현 보정 내역은 [README](../../README.md)에 있다. 기존 완료 이력·미수신 usage ledger를 지우지 않고 재사용하며 새 모델 호출 없이 분석하려면 replay.py, revalidate.py --summarize-only, audit.py, analyze.py, figures.py 순서로 실행한다.',
        '', '공식 규칙: https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena — 공개 Space는 UI이고 채점 worker는 별도다. 로컬 계측은 공식 worker 동등성이 확인된 결과가 아니다.',
        '', 'Proof token은 각 고정 환경의 Lean lexer로 직접 센 로컬 값이다. 데이터셋의 proof_length와 다른 문제가 있어 baseline_comparison.json에 대조했다. 감소율의 분모는 동일 로컬 방식으로 측정한 원본이며 공식 채점과 같다고 주장하지 않는다.',
        '', '구독/API 비용 구분: https://learn.chatgpt.com/docs/pricing — 구독 token을 API 목록 가격으로 환산하여 실제 지출이라고 보고하지 않았다.']
    for name,label in [('performance_summary','P-A 조건별 로컬 지표와 문제별 평균'),('tradeoff','유효 생성 후보의 지표 상충관계'),('selection_tradeoff','이력별 동일 후보군의 선택 정책 비교'),
        ('token_budget_curve','실제 model token에 따른 이용 가능 best'),('feedback_success','손상 proof의 복구 성공률')]:
        if (run/'figures'/f'{name}.png').exists():lines+=['',f'![{label}](figures/{name}.png)',f'[SVG 내려받기](figures/{name}.svg)']
    (run/'REPORT.md').write_text('\n'.join(lines)+'\n')
    try:
        import markdown
        rendered=markdown.markdown('\n'.join(lines),extensions=['tables','fenced_code'])
    except ImportError:rendered='<pre>'+html.escape('\n'.join(lines))+'</pre>'
    (run/'report.html').write_text('<!doctype html><html lang="ko"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Lean experiment</title><style>body{font:16px system-ui;max-width:1100px;margin:40px auto;padding:0 18px;line-height:1.65;color:#182230}pre{white-space:pre-wrap}a{color:#1260ad}img{max-width:100%;height:auto}table{border-collapse:collapse;width:100%;font-size:14px}td,th{border:1px solid #d7dce2;padding:7px;text-align:left}th{background:#f1f4f7}code{overflow-wrap:anywhere}</style><p><a href="REPORT.md">Markdown</a> · <a href="analysis/status.json">Status JSON</a></p>'+rendered+'</html>')
    log('analysis_updated',**status)

if __name__=='__main__':main()
