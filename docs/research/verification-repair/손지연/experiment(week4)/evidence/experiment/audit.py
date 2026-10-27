"""Cross-check model accounting, effective worker versions and immutable originals."""
from collections import Counter
import json
from common import HERE,read,write,run_dir,sha,package_hashes,log

INITIAL_ENGINE='eaea4574da18005ff9e79b08a93242b865c016b7b9527452000671578aaeb540'
CLARIFIED_ENGINE='3af10a0f3f6acc2fc6db45f233c5792328d634a0c52786981ec9275ccd23460f'

def effective_sources():
    values=[]
    for name,h in [('first-history.log',INITIAL_ENGINE),('P_A.log',INITIAL_ENGINE),('P_A-extra.log',CLARIFIED_ENGINE),('P_A-extra2.log',CLARIFIED_ENGINE),
        ('V_B.log',CLARIFIED_ENGINE),('V_B-extra.log',CLARIFIED_ENGINE),('V_B-extra2.log',CLARIFIED_ENGINE)]:
        file=HERE/name
        if not file.exists():continue
        for line in file.read_text().splitlines():
            try:r=json.loads(line)
            except ValueError:continue
            if r.get('event')!='history_complete':continue
            dest=run_dir()/'runs'/r['family']/f"P{r['problem']}"/(r['error'] or 'normal')/r['condition']/f"repeat_{r['repeat']}"
            value=dict(worker_log=name,effective_engine_sha256=h,source_snapshot=str(HERE/'snapshots/runner_sources'/f'{h}.py'),
                note='run_manifest adapter_hashes capture files on disk at history start; this supplement identifies the code loaded by the persistent worker.')
            write(dest/'effective_runner.json',value);values.append(dict(path=str(dest),**value))
    return values

def main():
    run=run_dir();versions=effective_sources();calls=[];threads=[];tools=[];mismatches=[];unknown=[];redaction=[];multiple_turns=[]
    for path in sorted((run/'runs').glob('*/*/*/*/*/model_ledger.json')):
        ledger=read(path);s=ledger['snapshot'];entries=ledger['entries']
        if len(entries)!=s['calls']:mismatches.append(dict(path=str(path),field='calls'))
        counted=sum((e.get('usage') or {}).get('input_tokens',0)+(e.get('usage') or {}).get('output_tokens',0) for e in entries)
        if counted!=s['tokens']:mismatches.append(dict(path=str(path),field='tokens'))
        for e in entries:
            calls.append(dict(history=str(path.parent),**e))
            if e['state']!='completed':unknown.append(dict(history=str(path.parent),call=e['call'],state=e['state']))
            tools.extend(e.get('tool_events',[]))
            directory=path.parent/'model_calls'/f'{e["call"]:02d}'
            request=directory/'request.json'
            if request.exists() and '/Users/' in request.read_text():redaction.append(str(request))
            stream=directory/'process/stdout.log'
            if stream.exists():
                completions=[]
                for line in stream.read_text(errors='replace').splitlines():
                    try:event=json.loads(line)
                    except ValueError:continue
                    if event.get('type')=='thread.started':threads.append(event['thread_id'])
                    if event.get('type')=='turn.completed':completions.append(event)
                if len(completions)>1:multiple_turns.append(dict(history=str(path.parent),call=e['call'],completed_turns=completions))
    protocol=read(run/'protocol.json')
    selected_mismatches=[];candidate_mismatches=[];selected_checked=0;candidate_checked=0
    initial_input_mismatches=[];v_pairs={};initial_inputs_checked=0
    for path in (run/'runs').glob('*/*/*/*/*/result.json'):
        result=read(path)
        config=read(path.parent/'config.json');first=path.parent/'model_calls/01/request.json'
        if first.exists():
            initial_inputs_checked+=1;request=read(first)
            body=config['original_body'] if result['family']=='P_A' else config['initial_body']
            if request['current_file']!=config['prefix']+body+config['suffix']:initial_input_mismatches.append(str(first))
        if result['family']=='V_B':
            key=(result['problem'],result['error_category'],result['repeat'])
            v_pairs.setdefault(key,{})[result['condition']]={k:config[k] for k in ('initial_body','initial_facts','prefix','suffix','target','baseline_metrics','max_calls')}
        if result['verified']:
            selected_checked+=1;proof=path.parent/'selected.proof.lean'
            if not proof.exists() or sha(proof.read_bytes())!=result['selected_sha256']:selected_mismatches.append(str(path))
        for cfile in (path.parent/'candidates').glob('*/candidate.json'):
            candidate_checked+=1;c=read(cfile)
            if sha(c['body'])!=c['proof_sha256']:candidate_mismatches.append(str(cfile))
    overruns=[]
    for path in (run/'runs').glob('*/*/*/*/*/model_ledger.json'):
        snapshot=read(path)['snapshot']
        if snapshot['tokens']>snapshot['max_model_tokens']:
            terminal=read(path.parent/'result.json')
            overruns.append(dict(history=str(path.parent),known_tokens=snapshot['tokens'],soft_limit=snapshot['max_model_tokens'],
                exceeded_by=snapshot['tokens']-snapshot['max_model_tokens'],stop_after_detection=terminal['stop_reason']=='subscription_token_limit'))
    lean_records=[]
    lean_by_area=Counter()
    for folder in ('baseline','V_A','runs','holdout_baseline','holdout_checks','revalidation','controls','module_audit_probe','module_audit_probe_retry2','module_audit_probe_retry3'):
        for path in (run/folder).rglob('process.json'):
            value=read(path)
            if 'lean' in value.get('argv',[]):
                lean_records.append(dict(path=str(path),returncode=value.get('returncode'),timeout=value.get('timeout'),elapsed_ms=value.get('elapsed_ms')))
                lean_by_area[folder]+=1
    result=dict(actual_calls=len(calls),known_model_tokens=sum((e.get('usage') or {}).get('input_tokens',0)+(e.get('usage') or {}).get('output_tokens',0) for e in calls),
        accounting_mismatches=mismatches,in_flight_or_unknown=unknown,tool_events=tools,redaction_failures=redaction,
        distinct_threads=len(set(threads)),thread_events=len(threads),duplicate_threads=[k for k,n in Counter(threads).items() if n>1],
        invocations_with_multiple_completed_turns=multiple_turns,
        selected_proof_files_checked=selected_checked,selected_file_hash_mismatches=selected_mismatches,
        submitted_candidate_files_checked=candidate_checked,saved_candidate_hash_mismatches=candidate_mismatches,
        initial_model_inputs_checked=initial_inputs_checked,initial_model_input_mismatches=initial_input_mismatches,
        v_feedback_input_pairs_checked=len(v_pairs),v_feedback_input_pair_mismatches=[list(k) for k,v in v_pairs.items() if set(v)!=set(('B1','B2')) or v['B1']!=v['B2']],
        unknown_usage_calls=[item for item in unknown if item['state']=='unknown_usage'],
        soft_token_budget_overruns=overruns,total_model_tokens=None if unknown else sum((e.get('usage') or {}).get('input_tokens',0)+(e.get('usage') or {}).get('output_tokens',0) for e in calls),
        original_package_unchanged=package_hashes()==protocol['original_package_hashes'],
        dataset_unchanged=sha((HERE/'benchmark_data_warmup.jsonl').read_bytes())==protocol['dataset_sha256'],
        design_unchanged=sha((HERE/'DESIGN.md').read_bytes())==protocol['design_sha256'],effective_sources=versions,
        verification_lean_process_records=len(lean_records),verification_lean_process_records_by_area=dict(lean_by_area),
        lean_timeout_records=sum(bool(r['timeout']) for r in lean_records),
        lean_count_scope='Completed verifier/auditor subprocess records, including failed probes/retries/controls; excludes dependency build/cache commands and still-running processes.',
        api_spend_usd=None,closed_track_compliant=False)
    write(run/'analysis/audit.json',result);log('audit',calls=len(calls),accounting_mismatches=len(mismatches),tool_events=len(tools),redaction_failures=len(redaction),
        original_package_unchanged=result['original_package_unchanged'],duplicate_threads=len(result['duplicate_threads']))

if __name__=='__main__':main()
