"""Premodel correction of an unintended broken parser boundary; preserve rejected preflight."""
import argparse
import difflib
import re
import shutil
from common import read,write,run_dir,sha,append
from tasks import task,make,base_env

def main(p):
    run=run_dir();existing=list((run/'runs/V_B'/f'P{p}'/'proof_error').glob('B*/repeat_*/model_ledger.json'))
    if existing:raise RuntimeError('Do not change a fixture after any model invocation in that category')
    old=run/'V_A'/f'P{p}'/'proof_error.json'
    result=read(old)
    if result['actual_status']!='invalid_candidate' or result['A3_result']['failure_kind']!='syntax':raise ValueError('not the unintended parser-boundary case')
    archive=run/'preflight_rejected'/f'P{p}'/'proof_error';archive.mkdir(parents=True)
    original=task(p);broken=task(p,'proof_error')
    shutil.copyfile(old,archive/'V_A_result.json')
    shutil.copyfile(broken.source.parent/'task.json',archive/'task.json')
    shutil.copyfile(broken.source,archive/'source.lean')
    shutil.copyfile(run/'fixtures'/f'P{p}'/'proof_error.lean',archive/'candidate.lean')
    # Remove the readiness signal while constructing the replacement, before any model call.
    old.rename(archive/'canonical_readiness_record.json')
    body=original.initial_body
    matches=re.finditer(r'\b(?:exact|apply|refine)\s+(?:\(\s*)?([A-Za-z_][\w\'.]*)',body)
    match=next(m for m in matches if m[1] not in {'by','fun','match','show','if','let'})
    new=body[:match.start(1)]+'experiment_missing_lemma'+body[match.end(1):]
    fixed=make(p,base_env(p),'proof_error_v2',text=original.text,body=new)
    fixed.config['limits'].update(original.limits);write(fixed.source.parent/'task.json',fixed.config)
    # The canonical input config redirects to the new immutable source; old bytes remain archived.
    write(broken.source.parent/'task.json',fixed.config)
    (run/'fixtures'/f'P{p}'/'proof_error.diff').write_text(''.join(difflib.unified_diff(body.splitlines(True),new.splitlines(True),fromfile='normal',tofile='proof_error_v2')))
    append(run/'fixture_amendments.jsonl',dict(problem=p,category='proof_error',before_model_invocations=True,
        reason='Initial whole-tactic-line mutation accidentally deleted a parenthesized multiline term boundary. Preserve the complete term and replace only its actual referenced identifier.',
        changed_identifier=match[1],original_rejected_record=str(archive),new_source=str(fixed.source),new_source_sha256=sha(fixed.text),
        original_V_A_status=result['actual_status'],new_expected_status='proof_error',both_model_conditions_identical=True))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('problem',type=int);args=parser.parse_args();main(args.problem)
