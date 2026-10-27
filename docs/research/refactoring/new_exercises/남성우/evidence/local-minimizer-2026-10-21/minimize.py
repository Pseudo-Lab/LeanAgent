"""Bounded AST-guided local minimization. No model calls; source edits only.

Search on the first listed version. Revalidate the complete improvement pool
on every listed version before scoring. No measurements from search queries
are eligible for selection. All offsets are UTF-8 byte offsets from Lean.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path
import verifier as v
from proof_tokens import proof_length

HERE = Path(__file__).resolve().parent
ROWS = [json.loads(s) for s in (HERE/'warmup.jsonl').read_text().splitlines()]
CONTROLS = json.loads((HERE/'control_selected.json').read_text())
PROFILE = (HERE/'Profile.lean').read_text().removeprefix('import Lean\n')
POLICY = {'max_attempts': 24, 'max_rounds': 3, 'sites_per_round': 4,
          'operators': ['delete', 'simp?', 'exact?', 'aesop?', 'assumption', 'rfl'],
          'rank': 'two largest sequences and two largest standalone tactics per round; stable byte offsets',
          'selection': 'strict score improvement; query scripts excluded',
          'excluded_problem_ids': [8], 'model_calls': 0}


def body_tokens(row, body):
    return proof_length(row['statement']+' := '+body, row['statement'])


def score(tokens, hb, base_tokens, base_hb, passed=1, total=1):
    return (100*(1-tokens/base_tokens)+100*(1-hb/base_hb)+100*passed/total)/3


def patch(body, a, b, replacement):
    raw = body.encode()
    return (raw[:a]+replacement.encode()+raw[b:]).decode()


def profile(row, project, version, body, dest, ctx):
    source, a, b, ds, original = ctx
    # Documentation comments attach only to declaration syntax, not the wrapper.
    # Convert them to equal-length ordinary comments in this diagnostic copy only.
    prefix = source[:ds]
    doc_start=prefix.rfind('/--')
    if doc_start>=0 and re.fullmatch(r'/--[\s\S]*?-/\s*',prefix[doc_start:]):
        prefix=prefix[:doc_start]+'/- '+prefix[doc_start+3:]
    # Imports must precede declarations, including on `module` files.
    lines = prefix.splitlines(True)
    k = next((i+1 for i,l in enumerate(lines) if l.strip()=='module'), 0)
    lines.insert(k, 'import Lean\n')
    # Keep helper declarations outside sections and before theorem docstrings.
    # Module-system Lean requires compile-time code to be marked meta.
    helper=PROFILE
    if any(l.strip()=='module' for l in lines):
        helper=helper.replace('partial def minWalk','public meta partial def minWalk')
    last_import=max(i for i,l in enumerate(lines) if re.match(r'^(?:public\s+)?(?:meta\s+)?import\s',l))
    lines.insert(last_import+1,helper+'\n')
    prefix = ''.join(lines)+'\n#min_profile\n'+source[ds:a]
    text = prefix+body+'\n#exit\n'
    rc, out, err = v.invoke(project, text, dest)
    offset = len(prefix.encode())
    nodes = []
    for kind, first, last, depth in re.findall(r'MIN_AST\|([^|\s]+)\|(\d+)\|(\d+)\|(\d+)', out):
        start, end = int(first)-offset, int(last)-offset
        if 0 <= start < end <= len(body.encode()):
            nodes.append({'kind':kind, 'start':start, 'end':end, 'depth':int(depth)})
    result={'returncode':rc,'body_hash':v.sha(body),'nodes':nodes,'coordinate_unit':'utf8_bytes',
            'source':'Lean parser original Syntax; no semantic dependency claim'}
    v.save(dest.with_suffix('.ast.json'), result)
    if rc != 0:
        raise RuntimeError('AST profile failed: '+str(dest))
    return nodes


def sites(body, nodes):
    """Only complete tactic sequences and full-line tactic nodes.

    Selecting a parent node prevents children of that site dominating a round.
    Replacements preserve surrounding indentation; punctuation is never guessed.
    """
    raw=body.encode(); found={}
    supported={'tacticSeq1Indented','tacticHave__','tacticLet__','simp','simpAll',
               'rwSeq','rewriteSeq','exact','apply','refine','intros','intro','renameI',
               'assumption','rfl','constructor','«tactic_<;>_»'}
    for n in nodes:
        a,b=n['start'],n['end']; kind=n['kind'].rsplit('.',1)[-1]
        left=raw[raw.rfind(b'\n',0,a)+1:a]
        endline=raw.find(b'\n',b)
        right=raw[b:endline if endline>=0 else len(raw)]
        if kind not in supported or left.strip() or right.strip():
            continue
        if len(raw[a:b].strip()) < 8:
            continue
        found[(a,b)]={**n,'text':raw[a:b].decode()}
    ranked=sorted(found.values(),key=lambda n:(-(n['end']-n['start']),n['start']))
    # Include nested sites: full-body solver failures must not prevent smaller edits.
    selected=[]
    for n in ranked:
        if any(n['start']==x['start'] and n['end']==x['end'] for x in selected):continue
        selected.append(n)
    return selected


def suggestion(output, line):
    """Conservative one-line extraction, linked to the queried source line.
    Multi-line scripts are deliberately unsupported in this initial experiment.
    Full revalidation protects against false/incomplete single-line suggestions.
    """
    messages=re.split(r'(?m)^(?=.+\.lean:\d+:\d+: (?:information|info|warning|error):)',output)
    for msg in messages:
        pos=re.search(r'\.lean:(\d+):\d+:',msg)
        if not pos or int(pos[1])!=line:continue
        m=re.search(r'Try this:\s*(?:\[apply\]\s*)?([^\n]+)',msg)
        if m:
            s=m[1].strip()
            if s.startswith(('simp only','simp_all only','exact ','aesop ')) and not re.search(r'\b(sorry|admit)\b',s):
                return s
    return None


def eligible(obs, baseline):
    return (obs.get('kind')=='valid' and obs.get('heartbeats') is not None
            and set(obs.get('axioms') or []) <= set(baseline.get('axioms') or []))


def run_problem(n, project, version):
    row=ROWS[n-1]; versions=[k for d in row['version_info'] for k in d]
    d=HERE/'runs'/f'{n:02d}'/version; d.mkdir(parents=True,exist_ok=True)
    if (d/'result.json').exists():
        print('RESUME completed',n,version,flush=True);return
    ctx=v.context(row,project,version)
    pin=next(x[version] for x in row['version_info'] if version in x)
    actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=project,text=True).strip()
    toolchain=(project/'lean-toolchain').read_text().strip()
    if actual!=pin or toolchain!='leanprover/lean4:'+version:
        raise RuntimeError(f'Environment pin mismatch {n}: {actual}, {toolchain}')
    is_primary=version==versions[0]
    baseline=v.check(row,project,version,ctx[-1],d/'baseline',ctx,measure=is_primary)
    if baseline['kind']!='valid' or (is_primary and not baseline.get('heartbeats')):
        v.save(d/'blocked.json',baseline);raise RuntimeError(f'Baseline unavailable {n} {version}')
    control_body=CONTROLS[n-1]['proof_body']
    control=baseline if control_body==ctx[-1] else v.check(row,project,version,control_body,d/'control',ctx,measure=is_primary)
    result={'problem_id':n,'name':row['name'],'version':version,'commit':pin,
            'source_hash':v.sha(ctx[0]),'baseline':baseline,'control':control,'attempts':[], 'pool':[]}
    catalog=HERE/'pool'/f'{n:02d}.json'
    if version!=versions[0]:
        if not catalog.exists():raise RuntimeError('Run primary first')
        for j,item in enumerate(json.loads(catalog.read_text())):
            obs=v.check(row,project,version,item['body'],d/f'pool_{j:02d}',ctx,measure=False)
            result['pool'].append({**item,'observation':obs})
        v.save(d/'result.json',result);print('VERSION DONE',n,version,flush=True);return
    if not eligible(control,baseline):
        raise RuntimeError('Control invalid or new axioms; do not silently change comparison')
    incumbent_body=control_body; incumbent=control
    if score(control['tokens'],control['heartbeats'],baseline['tokens'],baseline['heartbeats'])<100/3:
        incumbent_body=ctx[-1];incumbent=baseline
    pool=[]; seen={v.sha(control_body),v.sha(ctx[-1])}; count=0
    if n not in POLICY['excluded_problem_ids']:
        for round_no in range(POLICY['max_rounds']):
            nodes=profile(row,project,version,incumbent_body,d/f'profile_{round_no}',ctx)
            candidates=sites(incumbent_body,nodes)
            # Rotate past earlier large sites after each accepted mutation.
            seq=[s for s in candidates if 'tacticSeq' in s['kind']][:2]
            atom=[s for s in candidates if 'tacticSeq' not in s['kind']][:2]
            chosen=seq+atom
            before=incumbent_body; best_body=before; best=incumbent
            for site in chosen:
                for op in POLICY['operators']:
                    if count>=POLICY['max_attempts']:break
                    if op=='delete' and 'tacticSeq' in site['kind']:continue
                    if op=='aesop?' and row['source']=='strata':continue
                    repl='' if op=='delete' else op
                    body=patch(before,site['start'],site['end'],repl)
                    if v.sha(body) in seen:continue
                    seen.add(v.sha(body));count+=1
                    dest=d/f'a{count:03d}'
                    obs=v.check(row,project,version,body,dest,ctx,measure=not op.endswith('?'))
                    attempt={'id':count,'round':round_no,'parent_hash':v.sha(before),'site':site,
                             'operator':op,'query_hash':v.sha(body),'query_observation':obs}
                    if op.endswith('?'):
                        output=Path(obs['output_path']).read_text() if obs.get('output_path') else ''
                        line=(ctx[0][:ctx[1]].encode()+before.encode()[:site['start']]).count(b'\n')+1
                        s=suggestion(output,line)
                        if s:
                            body=patch(before,site['start'],site['end'],s)
                            obs=v.check(row,project,version,body,Path(str(dest)+'_explicit'),ctx)
                            attempt.update(suggestion=s,explicit_observation=obs)
                        else:
                            attempt['outcome']='no_supported_suggestion';result['attempts'].append(attempt)
                            v.save(d/'progress.json',result);continue
                    if eligible(obs,baseline):
                        value=score(obs['tokens'],obs['heartbeats'],baseline['tokens'],baseline['heartbeats'])
                        attempt.update(score=value,body_hash=v.sha(body),outcome='valid')
                        # Preserve all valid explicit proposals for final cross-version selection.
                        item={'body':body,'body_hash':v.sha(body),'attempt_id':count,'operator':op,
                              'primary_score':value,'observation':obs}
                        if not any(x['body_hash']==item['body_hash'] for x in pool):pool.append(item)
                        if value>score(best['tokens'],best['heartbeats'],baseline['tokens'],baseline['heartbeats']):
                            best_body,best=body,obs
                    else:attempt['outcome']=obs['kind'] if obs['kind']!='valid' else 'new_axioms_or_unmeasured'
                    result['attempts'].append(attempt);v.save(d/'progress.json',result)
                    print('ATTEMPT',n,count,op,attempt['outcome'],attempt.get('score'),flush=True)
                if count>=POLICY['max_attempts']:break
            incumbent_body,incumbent=best_body,best
            if incumbent_body==before or count>=POLICY['max_attempts']:break
    result['pool']=pool
    v.save(catalog,[{k:z for k,z in x.items() if k!='observation'} for x in pool])
    v.save(d/'result.json',result)
    print('PRIMARY DONE',n,version,'valid proposals',len(pool),flush=True)


def main():
    p=argparse.ArgumentParser();p.add_argument('project',type=Path);p.add_argument('version');p.add_argument('ids',type=int,nargs='+')
    args=p.parse_args();v.save(HERE/'policy.json',POLICY)
    for n in args.ids:run_problem(n,args.project.resolve(),args.version)

if __name__=='__main__':main()
