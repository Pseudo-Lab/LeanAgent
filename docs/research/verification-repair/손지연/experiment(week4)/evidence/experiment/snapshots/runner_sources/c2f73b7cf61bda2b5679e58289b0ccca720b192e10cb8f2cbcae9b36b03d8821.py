"""Immutable per-version source tasks and explicit, independently labelled fixtures."""
import difflib
import math
import re
from pathlib import Path
from common import HERE, ROOT, read, write, rows, git, sha, run_dir, log
from prepare import family, inventory
from lean_repair.contracts import TaskSpec
from lean_repair.runtime import Trace, ProcessRunner
from verifier import ExperimentVerifier

def boundaries(row,text):
    src=row['src'].rstrip()
    if src in text:start=text.index(src);end=start+len(src)
    else:
        # P10's older pinned releases differ only by whitespace in the original body.
        # Match identical non-whitespace text; retain the release's actual source bytes.
        pattern=r'\s+'.join(re.escape(s) for s in re.split(r'\s+',src))
        matches=list(re.finditer(pattern,text))
        if len(matches)!=1:raise ValueError('cannot bind dataset proof to one unchanged-token source span')
        start,end=matches[0].span()
    marker=row['statement']+' := ';assert src.startswith(marker+'by')
    assert text.startswith(marker+'by',start)
    a=start;b=start+len(marker);c=end
    scoped=list(re.finditer(r'^(?:set_option [^\n]+ in|omit \[[^\n]+ in)\s*$',text[:start],re.M))
    if scoped:
        tail=text[scoped[-1].end():start]
        if not re.search(r'\b(?:theorem|lemma|def)\s',re.sub(r'/-.*?-/', '',tail,flags=re.S)):a=scoped[-1].start()
    end=len(text[:a].rstrip())
    if text[end-2:end]=='-/':
        depth=1;pos=end-2
        while pos>0 and depth:
            opening=text.rfind('/-',0,pos);closing=text.rfind('-/',0,pos)
            if opening>closing:depth-=1;pos=opening
            else:depth+=1;pos=closing
            if pos<0:raise ValueError('unbalanced comment')
        if text[pos:pos+3]=='/--':a=pos
    return a,b,c

def make(p,env,name='main',text=None,body=None):
    folder=run_dir()/'inputs'/f'P{p}'/env['id']/name
    config_file=folder/'task.json'
    if config_file.exists():return TaskSpec.load(config_file)
    row=rows()[p-1];project=Path(env['project'])
    text=text if text is not None else ((project/row['file_path']).read_text() if row['file_path'] else row['header']+row['src'].rstrip()+'\n')
    a,b,c=boundaries(row,text)
    if body is not None:text=text[:b]+body+text[c:];c=b+len(body)
    folder.mkdir(parents=True);source=folder/'source.lean';source.write_text(text)
    config=dict(task_id=f'P{p}',target=row['name'],source=str(source),project=str(project),
        span=dict(declaration_start=a,body_start=b,body_end=c),
        pins=dict(source_sha256=sha(text),toolchain=(project/'lean-toolchain').read_text().strip(),
            manifest_sha256=sha((project/'lake-manifest.json').read_bytes()),project_commit=git(project,'rev-parse','HEAD'),
            fixed_context=dict(prefix_chars=b,suffix_chars=len(text)-c,prefix_sha256=sha(text[:b]),suffix_sha256=sha(text[c:]))),
        limits=dict(repair_calls=3,lean_seconds=300,model_seconds=300,task_seconds=5400,setup_seconds=1800,max_heartbeats=200000,infra_retries=1))
    write(config_file,config);return TaskSpec.load(config_file)

def base_env(p):
    f=family(p);version=read(run_dir()/'protocol.json')['base_versions'][f]
    return inventory()[f'{f}-{version}']

def task(p,name='main',env=None):
    e=env or base_env(p)
    return TaskSpec.load(run_dir()/'inputs'/f'P{p}'/e['id']/name/'task.json')

def backend(dest,t,seconds=5400):
    dest=Path(dest)
    if dest.exists():
        n=2
        while dest.with_name(dest.name+f'_retry{n}').exists():n+=1
        dest=dest.with_name(dest.name+f'_retry{n}')
    trace=Trace(dest);runner=ProcessRunner(trace,seconds)
    return trace,runner,ExperimentVerifier(t,runner)

def broken(p,body):
    # Target actual proof instructions, not an unrelated synthetic Nat declaration.
    special={7:('ih_l rfl l',"ih_l rfl der'"),12:('exact h_correlated_agreement','exact hprob_gt')}
    if p in special:
        old,new=special[p];assert old in body;return body.replace(old,new,1)
    # Replace one actual exact/apply/refine invocation with an unavailable lemma.
    match=re.search(r'(?m)^(\s*)(?:exact|apply|refine)\s+[^\n]+',body)
    if match:return body[:match.start()]+match[1]+'exact experiment_missing_lemma'+body[match.end():]
    # Some proofs only rewrite/transform: replace the first real tactic instruction.
    match=re.search(r'(?m)^(\s*)(?:rw|simp|simpa|rintro|intro|rcases|induction|constructor|convert|unfold|obtain)\b[^\n]*',body)
    if not match:raise ValueError(f'no eligible real proof tactic for P{p}')
    return body[:match.start()]+match[1]+'exact experiment_missing_lemma'+body[match.end():]

def initialize(p):
    env=base_env(p);t=make(p,env)
    bodies=dict(proof_error=broken(p,t.initial_body),incomplete='by\n  skip')
    for name,body in bodies.items():
        make(p,env,name,text=t.text,body=body)
        dest=run_dir()/'fixtures'/f'P{p}';dest.mkdir(parents=True,exist_ok=True)
        (dest/f'{name}.diff').write_text(''.join(difflib.unified_diff(t.initial_body.splitlines(True),body.splitlines(True),fromfile='normal',tofile=name)))
    row=rows()[p-1];src_start=t.text.index(row['src'].rstrip())
    declared=re.search(r'\b(?:theorem|lemma)\s+([\w\'.]+)',row['statement'])[1]
    helper=row['statement'].replace(declared,'experiment_gap_helper',1)
    decorator=t.text[t.declaration_start:src_start]
    fixture=t.text[:t.declaration_start]+decorator+helper+' := by\n  sorry\n\n'+t.text[t.declaration_start:]
    make(p,env,'indirect_fixture',text=fixture)
    write(run_dir()/'fixtures'/f'P{p}'/'expected.json',dict(correct='verified',proof_error='proof_error',incomplete='incomplete',
        direct_sorry='incomplete',changed_statement='invalid_candidate',indirect_sorry='incomplete',
        source='Labels assigned from controlled transformations, independently of proposed verifier outputs.'))
    return t

def calibrate(p):
    dest=run_dir()/'calibration'/f'P{p}.json'
    if dest.exists():return read(dest)
    t=initialize(p);trace,runner,v=backend(run_dir()/'baseline'/f'P{p}',t)
    prepared=v.prepare();write(trace.directory/'prepare.json',prepared.to_dict())
    if prepared.status!='candidate_pass':
        write(run_dir()/'failures'/f'P{p}_baseline.json',prepared.to_dict());log('baseline_failed',problem=p,status=prepared.status);return None
    result=v.verify(t.initial_body,'baseline','reference')
    if result.status!='candidate_pass':
        write(run_dir()/'failures'/f'P{p}_baseline.json',result.to_dict());log('baseline_failed',problem=p,status=result.status);return None
    cap=max(200000,math.ceil(1.25*result.metrics['heartbeats']))
    for name in ('main','proof_error','incomplete','indirect_fixture'):
        tt=task(p,name);tt.config['limits']['max_heartbeats']=cap;write(tt.source.parent/'task.json',tt.config)
    value=dict(problem=p,environment_id=v.environment_id,environment=v.environment,verification=result.to_dict(),
        baseline_metrics=result.metrics,frozen_max_heartbeats=cap,proof_sha256=sha(t.initial_body))
    write(dest,value);log('baseline_ready',problem=p,metrics=result.metrics);return value

if __name__=='__main__':
    import argparse
    from concurrent.futures import ThreadPoolExecutor
    parser=argparse.ArgumentParser();parser.add_argument('--problems',type=int,nargs='+',default=list(range(1,16)));parser.add_argument('--workers',type=int,default=3)
    args=parser.parse_args()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:list(pool.map(calibrate,args.problems))
