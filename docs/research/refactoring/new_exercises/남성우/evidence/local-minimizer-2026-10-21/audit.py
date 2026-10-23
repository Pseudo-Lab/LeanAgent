"""Read-only consistency audit. Does not replace Lean validation."""
import hashlib
import json
import re
from pathlib import Path
from minimize import ROWS

HERE=Path(__file__).resolve().parent


def main():
    issues=[];checks=0
    freeze=json.loads((HERE/'freeze.json').read_text())
    for name,h in freeze['hashes'].items():
        checks+=1
        if hashlib.sha256((HERE/name).read_bytes()).hexdigest()!=h:issues.append('changed frozen input/code: '+name)
    pairs=0;attempts=0
    for n,row in enumerate(ROWS,1):
        versions=[v for p in row['version_info'] for v in p]
        primary=HERE/'runs'/f'{n:02d}'/versions[0]/'result.json'
        if not primary.exists():issues.append(f'P{n} primary missing');continue
        ref=json.loads(primary.read_text());attempts+=len(ref['attempts'])
        if len(ref['attempts'])>24:issues.append(f'P{n} budget exceeded')
        if n==8 and (ref['attempts'] or ref['pool']):issues.append('P8 exclusion violated')
        pool={p['body_hash']:p['body'] for p in ref['pool']}
        for version in versions:
            path=HERE/'runs'/f'{n:02d}'/version/'result.json'
            if not path.exists():issues.append(f'P{n} {version} missing');continue
            pairs+=1;r=json.loads(path.read_text())
            # Compare every emitted candidate's unchanged prefix/suffix directly
            # with the independently verified original full-file snapshot.
            original_path=path.parent/'baseline.lean'
            if original_path.exists():
                original_text=original_path.read_text();src=row['src']
                if original_text.count(src)!=1:
                    issues.append(f'P{n} {version} baseline declaration mismatch')
                else:
                    ds=original_text.index(src)
                    original_body=src[len(row['statement']):].lstrip()[2:].lstrip()
                    a=ds+len(src)-len(original_body);b=ds+len(src)
                    prefix=original_text[:a];suffix=original_text[b:]
                    for candidate in path.parent.glob('*.lean'):
                        if not re.fullmatch(r'(control|a\d+(?:_explicit)?|pool_\d+)\.lean',candidate.name):continue
                        checks+=1;text=candidate.read_text()
                        if not (text.startswith(prefix) and text.endswith(suffix)):
                            issues.append(f'changed statement/context: {candidate.relative_to(HERE)}')
            if r['baseline']['kind']!='valid':issues.append(f'P{n} baseline invalid')
            actual={p['body_hash']:p['body'] for p in r['pool']}
            if actual!=pool:issues.append(f'P{n} {version} pool mismatch')
            for h,body in actual.items():
                checks+=1
                if hashlib.sha256(body.encode()).hexdigest()!=h:issues.append(f'P{n} candidate hash mismatch')
                if any(t in body for t in ['simp?', 'exact?', 'aesop?']):issues.append(f'P{n} query in final pool')
    if (HERE/'results.json').exists():
        for r in json.loads((HERE/'results.json').read_text()):
            if r['status']!='complete':continue
            checks+=1
            if r['final_score']<r['control_score'] or r['final_score']<100/3:issues.append(f"P{r['id']} fallback regression")
    submission_path=HERE/'submission.jsonl'
    if submission_path.exists():
        entries=[json.loads(line) for line in submission_path.read_text().splitlines()]
        selected=json.loads((HERE/'selected.json').read_text())
        if len(entries)!=len(ROWS) or len(selected)!=len(ROWS):issues.append('submission coverage mismatch')
        for row,entry,choice in zip(ROWS,entries,selected):
            checks+=1
            original=row['src'][len(row['statement']):].lstrip()[2:].lstrip()
            expected=row['src'][:-len(original)]+choice['proof_body']
            if entry['name']!=row['name'] or entry['proof']!=expected:issues.append('submission declaration/body mismatch: '+row['name'])
    out={'checks':checks,'problem_version_pairs':pairs,'attempts':attempts,'issues':issues,
         'scope':'artifact integrity and score consistency; Lean results are preserved external evidence'}
    (HERE/'audit.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(out,ensure_ascii=False,indent=2))
    return bool(issues)

if __name__=='__main__':raise SystemExit(main())
