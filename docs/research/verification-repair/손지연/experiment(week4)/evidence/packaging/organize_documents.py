"""Create relative-link sharing documents from immutable evidence copies."""
from datetime import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
from zoneinfo import ZoneInfo
import markdown

HERE = Path(__file__).resolve().parent
SHARE = HERE.parents[6]
WARMUP = SHARE/'docs/research/refactoring/warmup/손지연'
IMPL = SHARE/'docs/research/verifier-guided-agent/손지연'
EXPERIMENT = WARMUP/'evidence/experiment'
RUN = EXPERIMENT/(EXPERIMENT/'LATEST_RUN').read_text().strip()
REFERENCE = Path('/private/tmp/lean-share-structure-20261024')
COMMIT = '5eb5a8c61350d59f1c2f0655c18387abb58cafe4'

def read(path): return json.loads(path.read_text())
def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    structure = REFERENCE/'docs__STRUCTURE.md'
    # Keep the original reference; resolve a guide outside this sharing scope upstream.
    reference_dest=HERE/'references/docs__STRUCTURE.md'
    reference_dest.parent.mkdir(exist_ok=True);reference_dest.write_bytes(structure.read_bytes())
    shared_structure=structure.read_text().replace('](research/refactoring/arena-guide.html)',
        f'](https://github.com/Pseudo-Lab/LeanAgent/blob/{COMMIT}/docs/research/refactoring/arena-guide.html)')
    (SHARE/'docs/STRUCTURE.md').write_text(shared_structure)
    for p in REFERENCE.iterdir():
        if p.name=='docs__STRUCTURE.md' or p.read_text().startswith('{"message":"Not Found"'): continue
        dest = HERE/'references'/p.name;dest.parent.mkdir(exist_ok=True);dest.write_bytes(p.read_bytes())
    write(HERE/'structure-reference.json',dict(commit=COMMIT,
        url=f'https://github.com/Pseudo-Lab/LeanAgent/blob/{COMMIT}/docs/STRUCTURE.md',
        structure_sha256=sha(structure),shared_structure_sha256=sha(SHARE/'docs/STRUCTURE.md'),
        local_adaptation='An Arena guide not included in this scope links to the pinned upstream page; rule text is preserved.',shared_at='2026-10-24',
        intended_paths=['docs/research/refactoring/warmup/손지연/','docs/research/verifier-guided-agent/손지연/'],
        existing_warmup_filenames_preserved=['report.md','report.html','metrics.json','presentation.html'],
        meeting='No new meeting was specified; no meeting/date attendance was invented.'))
    original_design = SHARE.parent/'week3/lean_verification_repair_starter/DESIGN.md'
    (IMPL/'evidence/design.md').write_bytes(original_design.read_bytes())
    write(IMPL/'evidence/design-source.json',dict(source='week3/lean_verification_repair_starter/DESIGN.md',sha256=sha(original_design)))
    text = (RUN/'REPORT.md').read_text()
    def relocate(match):
        target=match[1]
        if target.startswith(('https:','http:','#')):return match[0]
        return ']('+os.path.relpath((RUN/target).resolve(),WARMUP)+')'
    text=re.sub(r'\]\(([^)]+)\)',relocate,text)
    banner='''> 공유 정리: 2026-10-24. 원래 완료 보고서의 수치·결론을 유지하고 링크를 evidence 위치에 맞췄다. 이번 정리에서 새 모델·Lean 실행은 하지 않았다.
>
> [자료 안내](README.md) · [측정 요약](experiment-metrics.json) · [검증·수리 구현](../../../verifier-guided-agent/손지연/report.md) · [새 위치의 재생 명령](evidence/README.md)
'''
    text=text.replace('\n', '\n\n'+banner+'\n',1)
    (WARMUP/'verification-repair-experiment.md').write_text(text)
    style='body{font:16px/1.75 system-ui,sans-serif;max-width:1120px;margin:36px auto;padding:0 22px;color:#182238}a{color:#1558a8}img{max-width:100%;height:auto}pre{white-space:pre-wrap;overflow-wrap:anywhere;background:#f2f5f9;padding:14px}code{overflow-wrap:anywhere}table{border-collapse:collapse;font-size:14px;display:block;overflow:auto}th,td{border:1px solid #cdd6e3;padding:7px 10px}th{background:#eff3f8}blockquote{border-left:4px solid #517fba;padding-left:14px;color:#41516b}nav{position:sticky;top:0;background:white;border-bottom:1px solid #d5deeb;padding:10px 0}'
    html='<!doctype html><html lang="ko"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>손지연 Warm-up 15문제 검증·수리 실험</title><style>'+style+'</style></head><body><nav><a href="README.md">자료 안내</a> · <a href="verification-repair-experiment.md">Markdown</a> · <a href="#top">맨 위</a> · <a href="../../../verifier-guided-agent/손지연/report.md">구현 보고서</a></nav><main id="top">'+markdown.markdown(text,extensions=['tables','fenced_code','toc'])+'</main></body></html>'
    (WARMUP/'verification-repair-experiment.html').write_text(html)
    protocol=read(RUN/'protocol.json');completion=read(RUN/'completion.json');audit=read(RUN/'analysis/audit.json')
    environments=[{k:env[k] for k in ('id','family','version','commit','problems')} for env in read(RUN/'environment_manifest.json')]
    metrics=dict(schema_version=1,author='손지연',organized_at='2026-10-24',
        measured_run_id=RUN.name,measured_at_Asia_Seoul=datetime.fromtimestamp(completion['finalized_at'],ZoneInfo('Asia/Seoul')).isoformat(),
        scope=dict(problems=list(range(1,16)),P_A_histories=180,V_A_cases=90,V_B_histories=180,designated_problem_environment_pairs=36),
        source=dict(completion='evidence/experiment/'+str((RUN/'completion.json').relative_to(EXPERIMENT)),
                    protocol='evidence/experiment/'+str((RUN/'protocol.json').relative_to(EXPERIMENT)),
                    protocol_sha256=sha(RUN/'protocol.json'),dataset_sha256=protocol['dataset_sha256']),
        environments=environments,P_A=read(RUN/'analysis/summary.json'),V_A=read(RUN/'analysis/validation_comparison.json'),
        V_B=read(RUN/'analysis/feedback_comparison.json'),
        selected=dict(generated=96,original_fallback=84),
        accounting=dict(actual_model_calls=audit['actual_calls'],known_model_tokens=audit['known_model_tokens'],
            total_model_tokens=audit['total_model_tokens'],unknown_usage_calls=len(audit['unknown_usage_calls']),
            soft_token_overrun_histories=len(audit['soft_token_budget_overruns']),api_spend_usd=None,usd3_strict_compliance=None,
            official_score=None,arena_closed_track_compliant=False,authentication='Existing ChatGPT subscription; not OpenRouter API in this run'),
        record_replay=dict(histories=360,matched=360),fresh_lean_revalidation=dict(checks=1213,semantic_matches=1212),
        no_new_model_or_lean_execution_during_organization=True)
    write(WARMUP/'experiment-metrics.json',metrics)
    validation=read(IMPL/'evidence/verification-repair/validation.json')
    write(IMPL/'metrics.json',dict(schema_version=1,author='손지연',organized_at='2026-10-24',
        original_validation_date=validation['date_Asia_Seoul'],source='evidence/verification-repair/validation.json',
        source_sha256=sha(IMPL/'evidence/verification-repair/validation.json'),
        full_suite=dict(validation['full_suite'],log='evidence/verification-repair/validation-tests.log'),local_lean_versions=validation['local_lean_versions'],
        design_sections=validation['design_sections'],paid_api_requests=validation['paid_api_requests'],
        repl_runtime={k:validation['repl_runtime'][k] for k in ('repository','tag','commit','binary_sha256')},
        limits=validation['limits'],current_packaging_checks='evidence/packaging-checks.json',
        distinction='73 historical tests; current packaging checks and mock/unit tests are recorded separately.'))
    print(json.dumps(dict(report='verification-repair-experiment.md',html='verification-repair-experiment.html',metrics=2)))

if __name__=='__main__':main()
