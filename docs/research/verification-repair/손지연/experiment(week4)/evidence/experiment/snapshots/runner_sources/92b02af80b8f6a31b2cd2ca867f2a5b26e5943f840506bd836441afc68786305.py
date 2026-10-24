"""P-B/P-C and descriptive P/V summaries; USD/official metrics stay null."""
from collections import Counter,defaultdict
import csv
import html
import json
import statistics
from common import HERE,read,write,run_dir,sha,log
from prepare import inventory
from engine import rank

def average(values):
    values=[v for v in values if v is not None]
    return statistics.mean(values) if values else None

def compatibility(p,h):
    designated=[e['id'] for e in inventory().values() if p in e['problems']]
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
        r=read(path);r['path']=str(path.parent);histories.append(r)
        if r['family']!='P_A':continue
        config=read(path.parent/'config.json');p=r['problem']
        candidates=[config['original_candidate']]+[read(f) for f in sorted((path.parent/'candidates').glob('*/candidate.json'))]
        eligible={c['proof_sha256']:annotate(p,c) for c in candidates if c['eligible']}
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
            if event['event']=='candidate':
                b=event['budget'];h=event['best_sha256'];m=eligible[h]['measurement'] if h in eligible else None
                curves.append(dict(history=str(path.parent),problem=p,condition=r['condition'],repeat=r['repeat'],calls=b['calls'],model_tokens=b['tokens'],
                    best_sha256=h,search_score=m['search_score'] if m else None,available_at=event['at'],availability='validation_completed',api_spend_usd=None))
            elif event['event']=='model_error':
                b=event['budget'];last=curves[-1]
                curves.append(dict(history=str(path.parent),problem=p,condition=r['condition'],repeat=r['repeat'],calls=b['calls'],model_tokens=b['tokens'],
                    best_sha256=last['best_sha256'],search_score=last['search_score'],available_at=event['at'],availability='no_new_candidate_model_error',api_spend_usd=None))
        for checkpoint in (0.5,1.0,2.0,3.0):usd.append(dict(history=str(path.parent),usd_checkpoint=checkpoint,selected_sha256=None,score=None,
            status='not_measurable_subscription',reason='No actual per-call USD invoice; no API price conversion or fabricated zero.'))
    pvalues=[r for r in histories if r['family']=='P_A'];vvalues=[r for r in histories if r['family']=='V_B']
    summary=[]
    for condition in ('A0','A1','A2','A3'):
        values=[r for r in pvalues if r['condition']==condition];measure=[r.get('posthoc_measurement') or {} for r in values]
        summary.append(dict(condition=condition,completed=len(values),planned=45,verified=sum(r['verified'] for r in values),
            selected_generated=sum(r['selected_origin']=='generated' for r in values),selected_original=sum(r['selected_origin']=='original' for r in values),
            improved=sum((r.get('selected_measurement') or {}).get('search_score',0)>0 for r in values),
            mean_token_reduction=average(m.get('token_reduction_pct') for m in measure),mean_heartbeat_reduction=average(m.get('heartbeat_reduction_pct') for m in measure),
            mean_compatibility=average(m.get('compatibility') for m in measure),mean_local_score=average(m.get('local_score') for m in measure),
            compatibility_measured=sum(m.get('compatibility') is not None for m in measure),model_calls=sum(r['budget']['calls'] for r in values),
            model_tokens=sum(r['budget']['tokens'] for r in values),api_spend_usd=None,score_official=None,stop_reasons=dict(Counter(r['stop_reason'] for r in values))))
    vsummary=[]
    for condition in ('B1','B2'):
        for category in ('proof_error','incomplete'):
            values=[r for r in vvalues if r['condition']==condition and r['error_category']==category]
            vsummary.append(dict(condition=condition,error_category=category,completed=len(values),planned=45,verified=sum(r['verified'] for r in values),
                success_rate=sum(r['verified'] for r in values)/len(values) if values else None,
                mean_success_calls=average(r['budget']['calls'] for r in values if r['verified']),model_calls=sum(r['budget']['calls'] for r in values),
                model_tokens=sum(r['budget']['tokens'] for r in values),api_spend_usd=None,stop_reasons=dict(Counter(r['stop_reason'] for r in values))))
    acases=[read(p) for p in sorted((run/'V_A').glob('P*/*.json'))]
    validation=[]
    for judge in ('A1','A2','A3'):
        validation.append(dict(judge=judge,cases=len(acases),planned=90,
            false_accept=sum(not a['expected_valid'] and a[judge]=='accept' for a in acases),false_reject=sum(a['expected_valid'] and a[judge]=='reject' for a in acases),
            abstain=sum(a[judge]=='abstain' for a in acases),not_available=sum(a[judge]=='not_available' for a in acases)))
    # Count live/in-flight ledgers as well, so the total never hides discarded or unfinished calls.
    ledgers=[read(p) for p in (run/'runs').glob('*/*/*/*/*/model_ledger.json')]
    live_tokens=sum(x['snapshot']['tokens'] for x in ledgers);live_calls=sum(x['snapshot']['calls'] for x in ledgers)
    status=dict(run_id=run.name,baseline_problems=len(list((run/'calibration').glob('P*.json'))),designated_environments=len(inventory()),
        ready_environments=len(list((run/'preparation').glob('*_ready.json'))),designated_problem_environment_pairs=sum(len(e['problems']) for e in inventory().values()),
        P_A_completed=len(pvalues),P_A_planned=180,V_A_cases=len(acases),V_A_planned=90,V_B_completed=len(vvalues),V_B_planned=180,
        actual_model_calls=live_calls,actual_model_tokens=live_tokens,in_flight_or_uncertain_ledgers=sum(x['snapshot']['accounting_uncertain'] for x in ledgers),
        api_spend_usd=None,score_official=None,complete=len(pvalues)==180 and len(vvalues)==180 and len(acases)==90,
        experiments='New 15-problem integrated P/V experiment; previous v0/v1 excluded')
    for name,value in [('status',status),('summary',summary),('feedback_comparison',vsummary),('validation_comparison',validation),
        ('validation_label_mismatches',[a for a in acases if not a['expected_status_match']]),('selection_comparison',selection),('budget_curve',curves),
        ('usd_budget_checkpoints',usd),('candidate_measurements',candidate_rows),('histories',histories)]:
        write(run/'analysis'/f'{name}.json',value)
        if isinstance(value,list):csv_write(run/'analysis'/f'{name}.csv',value)
    lines=['# 실험 진행·결과 보고서','',f'실행: `{run.name}`. 상태: '+('주 실행 완료' if status['complete'] else '**실행 중 — 최종 결과 아님**')+'.',
        '',f'정상 원본 기준 검증 {status["baseline_problems"]}/15, 환경 {status["ready_environments"]}/15, P-A {len(pvalues)}/180, V-A {len(acases)}/90, V-B {len(vvalues)}/180.',
        '',f'실제 모델 호출 {live_calls}회, 확인된 입출력 token {live_tokens:,}. API USD 비용·공식 점수·USD 3 준수 여부는 측정 불가(null).',
        '', 'P는 정상 proof를 제공한 리팩터링이다. V는 통제된 proof 오류/미완성 변형을 사용하고 원본 정답 proof를 모델에게 숨겼다. 모든 모델은 기존 GPT 구독 인증으로 호출했다.',
        '', '기준 버전만 사용하는 H 모드다. 선택을 고정한 뒤 지정된 모든 버전에서 동일 proof bytes를 평가한다. P-B의 호환성/종합 점수 선택은 사후 분석이며 실제 선택을 바꾸지 않는다.',
        '', '| P-A | 완료/예정 | 생성 후보 선택 | 원본 유지 | 개선 | token 감소 평균 % | HB 감소 평균 % | 호환성 측정 |',
        '|---|---:|---:|---:|---:|---:|---:|---:|']
    def fmt(x):return '미측정' if x is None else f'{x:.2f}'
    for s in summary:lines.append(f'| {s["condition"]} | {s["completed"]}/45 | {s["selected_generated"]} | {s["selected_original"]} | {s["improved"]} | {fmt(s["mean_token_reduction"])} | {fmt(s["mean_heartbeat_reduction"])} | {s["compatibility_measured"]} |')
    lines+=['','| V-A | 검사 | 오수락 | 오거절 | 보류 | 관측 불가 |','|---|---:|---:|---:|---:|---:|']
    for s in validation:lines.append(f'| {s["judge"]} | {s["cases"]} | {s["false_accept"]} | {s["false_reject"]} | {s["abstain"]} | {s["not_available"]} |')
    lines+=['','| V-B | 오류 유형 | 완료/예정 | verified | 성공률 | 모델 호출 |','|---|---|---:|---:|---:|---:|']
    for s in vsummary:lines.append(f'| {s["condition"]} | {s["error_category"]} | {s["completed"]}/45 | {s["verified"]} | {fmt(100*s["success_rate"] if s["success_rate"] is not None else None)}% | {s["model_calls"]} |')
    lines+=['','직접 sorry는 패키지의 엄격 guard가 `invalid_candidate(policy)`로 거절할 수 있다. DESIGN의 기대 상태 `incomplete`와의 라벨 차이는 별도 파일에 기록하며, 이를 오수락과 혼동하지 않는다.',
        '', '15문제의 작은 개발 표본에 대한 기술통계다. 문제별 결과와 독립 반복을 보존하며, 정책·반복 간 후보를 하나의 예산 실행처럼 합치지 않는다.',
        '', '원시 기록: `runs/`, `baseline/`, `V_A/`, `compatibility/`. 분석: `analysis/summary.json`, `selection_comparison.json`, `budget_curve.json`, `record_replay.json`, `lean_revalidation.json`.',
        '', '공식 규칙: https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena — 공개 Space는 UI이고 채점 worker는 별도다. 로컬 계측은 공식 worker 동등성이 확인된 결과가 아니다.',
        '', '구독/API 비용 구분: https://learn.chatgpt.com/docs/pricing — 구독 token을 API 목록 가격으로 환산하여 실제 지출이라고 보고하지 않았다.']
    (run/'REPORT.md').write_text('\n'.join(lines)+'\n')
    (run/'report.html').write_text('<!doctype html><meta charset="utf-8"><title>Lean experiment</title><style>body{font:16px system-ui;max-width:1100px;margin:40px auto;line-height:1.6}pre{white-space:pre-wrap}a{color:#1260ad}</style><h1>Lean experiment</h1><p>See <a href="REPORT.md">REPORT.md</a> and <a href="analysis/status.json">status.json</a></p><pre>'+html.escape('\n'.join(lines))+'</pre>')
    log('analysis_updated',**status)

if __name__=='__main__':main()
