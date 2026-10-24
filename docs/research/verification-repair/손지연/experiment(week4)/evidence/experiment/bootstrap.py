"""Freeze a complete 15-problem subscription-only experiment before inference."""
from datetime import datetime
import shutil
from zoneinfo import ZoneInfo
from common import HERE, ROOT, rows, sha, write, package_hashes

def main():
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--new-run',action='store_true');args=parser.parse_args()
    if (HERE/'LATEST_RUN').exists():
        previous=HERE/(HERE/'LATEST_RUN').read_text().strip()
        if not args.new_run:raise SystemExit('An experiment exists; use resume commands, or --new-run after completion.')
        from common import read
        if not (previous/'completion.json').exists() or not read(previous/'completion.json').get('execution_complete'):
            raise SystemExit('Do not switch LATEST_RUN while an unfinished experiment may still have active workers.')
    shutil.copyfile(ROOT/'week2/benchmark_data_warmup.jsonl', HERE/'benchmark_data_warmup.jsonl')
    for name in ('verifier.py','quota.py'):
        shutil.copyfile(HERE.parent/'experiment-v1'/name, HERE/name)
    stamp=datetime.now(ZoneInfo('Asia/Seoul')).strftime('%Y%m%dT%H%M%S%z')
    run=HERE/'runs'/stamp; run.mkdir(parents=True)
    protocol=dict(run_id=stamp, design_sha256=sha((HERE/'DESIGN.md').read_bytes()),
        dataset_sha256=sha((HERE/'benchmark_data_warmup.jsonl').read_bytes()),
        dataset_resolution='DESIGN sibling path resolved to week2/benchmark_data_warmup.jsonl; byte-identical copy here',
        scope=list(range(1,16)), previous_runs='Preserved experiment-v0/v1 are NOT counted as new experiment executions.',
        authentication=dict(provider='OpenAI Codex CLI',method='ChatGPT subscription only',model='gpt-5.6-sol',reasoning='high',
            tools=False,api_fallback=False,purchased_credits=False,quota_stop_used_percent=90),
        money=dict(api_spend_usd=None,usd3_strict_compliance=None,score_official=None,
            reason='User chose included GPT subscription; no per-call USD invoice is exposed. API list-price conversion is not a subscription cost measurement.',
            arena_closed_track_compliant=False),
        mode='H: base-only search, immutable selection before holdout; holdout results never feed model calls',
        base_versions=dict(strata='v4.26.0',physlib='v4.32.0',cslib='v4.33.0-rc2',arklib='v4.31.0',mathlib='v4.26.0'),
        base_choice_reason='Reuse the pinned versions with exact dataset-source matches and previously established caches, before new model outcomes; evaluate every listed version separately.',
        P_A=dict(conditions=['A0','A1','A2','A3'],independent_repeats=3,planned_histories=180,
            calls=dict(A0=1,A1=3,A2=3,A3=3),soft_model_tokens=240000,
            A0='one proposal then freeze',A1='fresh independent proposals from the original; discard failures; no failed candidate or diagnostic feedback',
            A2='current proof and raw diagnostics, repair invalid candidates; continue after success',
            A3='A2 plus token/HB and base-only search-score feedback on successful candidates',
            best='maximize base search_score=(token_reduction_pct+heartbeat_reduction_pct)/2',
            tie=['proof_tokens','raw_heartbeats','proof_sha256'],fallback='verified original participates in every history and every policy',
            final_failure='freshly check next ranked eligible candidate, then original; never call model after freeze'),
        P_B=dict(policies=['min_tokens','min_heartbeats','max_compatibility','max_local_score'],
            candidate_scope='each individual P-A history including original fallback',extra_model_calls=0,
            holdout_selection='B3/B4 are post hoc; never replace the frozen P-A main selection'),
        P_C=dict(usd_checkpoints=[0.5,1.0,2.0,3.0],usd_results=None,
            additional_axes=['actual cumulative model calls','actual cumulative model tokens'],
            availability='Only after validation completion; include failed/discarded calls; original available at zero.'),
        V_A=dict(variants=['correct','proof_error','incomplete','direct_sorry','changed_statement','indirect_sorry'],
            planned_cases=90,expected_status=['verified','proof_error','incomplete','incomplete','invalid_candidate','incomplete'],
            truth='Independently assigned from fixture definitions, before executing the verifier.',
            judge_A2='native outer tactic goals_after; unavailable => not_available, never substitute diagnostics text',
            strict_guard_note='Unmodified reusable package rejects direct sorry as invalid_candidate(policy); report label mismatch separately from binary validity.'),
        V_B=dict(error_categories=['proof_error','incomplete'],variants_per_category=1,conditions=['B1','B2'],
            independent_repeats=3,planned_histories=180,max_calls=4,soft_model_tokens=240000,
            B1='raw text of the exact same diagnostic/goal/context facts',B2='structured facts and status-specific guidance',
            reference_hidden=True,stop='first freshly verified complete proof; otherwise limit/error',
            task_contract='Original TaskSpec repair_calls remains 3 (package maximum); experiment-local controller independently enforces four proposals.'),
        limits=dict(lean_seconds=300,model_seconds=300,history_seconds=5400,setup_seconds=1800,
            max_heartbeats='max(200000, ceil(1.25 * baseline heartbeat count)) per problem/environment, before inference',
            token_reservation='len(prompt_utf8)//3+16000; soft token cap; actual output length cannot be hard-capped through this subscription transport',
            repeated_candidate='stop after the same generated proof hash occurs twice in a history; preserve best',
            environment_error='stop that history, no proof-repair loop',model_error='record reservation/usage then stop; no silent retry'),
        V_C=dict(record_replay='pure reducer with stored requests, responses, outcomes, cost and elapsed events; zero subprocess/model calls',
            revalidate='fresh Lean checks for every unique saved submitted candidate in each base environment and every saved holdout candidate/environment',
            comparison=['status','proof_sha256','axioms','diagnostics','proof_tokens','raw_heartbeats','environment_id'],
            controls=['direct_sorry','indirect_sorry','statement_drift','repeated_candidate','real_process_timeout','environment_failure','malformed_model_output','reservation_boundary','valid_then_invalid']),
        scores=dict(token='100*(1-T/T0)',heartbeat='100*(1-H/H0)',compatibility='100*k/m; null if any environment unavailable',
            local_score='(token_reduction+heartbeat_reduction+compatibility)/3; no clipping',search_score='(token_reduction+heartbeat_reduction)/2',
            missing='null; never replace missing with zero'), original_package_hashes=package_hashes())
    write(run/'protocol.json',protocol)
    write(run/'egress_approval.json',dict(user_reply='기존 GPT 구독으로 실행 — 정상 proof 전송 포함',
        scope='All 15 public benchmark problems: normal proof and public context for P; corrupted proof, diagnostic/goals/context for V.',
        service='OpenAI Codex/ChatGPT using existing GPT subscription',excluded=['credentials','local absolute paths'],
        inherited='Previous explicit approvals cover public broken-proof inputs of all 15 problems.'))
    write(run/'dataset_manifest.json',[dict(problem=p,target=row['name'],source_sha256=sha(row['src']),version_info=row['version_info']) for p,row in enumerate(rows(),1)])
    (HERE/'LATEST_RUN').write_text(str(run.relative_to(HERE))+'\n')
    print(run)

if __name__=='__main__':main()
