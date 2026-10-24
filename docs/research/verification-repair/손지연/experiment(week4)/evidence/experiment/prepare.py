"""Restore every designated pinned environment; never update upstream pins."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import importlib.util
import subprocess
import time
from common import HERE, ROOT, rows, read, write, append, git, run_dir, log

spec=importlib.util.spec_from_file_location('old_prepare',HERE.parent/'experiment-v1/prepare.py')
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
source_imports=old.source_imports
URLS=dict(strata='https://github.com/strata-org/Strata.git',physlib='https://github.com/leanprover-community/physlib.git',
    cslib='https://github.com/leanprover/cslib.git',arklib='https://github.com/Verified-zkEVM/ArkLib.git',mathlib='https://github.com/leanprover-community/mathlib4.git')
REUSE={('strata','v4.26.0'):ROOT/'week4/experiment-v1/envs/strata',('physlib','v4.32.0'):ROOT/'week4/experiment-v1/envs/physlib',
    ('mathlib','v4.26.0'):ROOT/'week4/experiment-v1/envs/mathlib',('cslib','v4.33.0-rc2'):ROOT/'week2/P7/cslib-progress'}
for name,versions in [('cslib',['v4.31.0','v4.32.0']),('arklib',['v4.29.0','v4.30.0','v4.31.0'])]:
    for version in versions:REUSE[name,version]=ROOT/'week2/evaluation/envs'/f'{name}-{version}'

def family(p):return 'strata' if p<=3 else 'physlib' if p<=6 else 'cslib' if p<=9 else 'arklib' if p<=12 else 'mathlib'

def inventory():
    envs={}
    for p,row in enumerate(rows(),1):
        for version_info in row['version_info']:
            for version,commit in version_info.items():
                name=family(p);key=f'{name}-{version}'
                reusable=REUSE.get((name,version))
                project=reusable if reusable and (reusable/'.git').exists() else HERE/'envs'/key
                env=envs.setdefault(key,dict(id=key,family=name,version=version,commit=commit,url=URLS[name],
                    project=str(project),problems=[]))
                assert env['commit']==commit;env['problems'].append(p)
    return envs

def command(argv,cwd,path,timeout=7200):
    path.parent.mkdir(parents=True,exist_ok=True);began=time.time()
    with path.open('a') as out:
        out.write('\n$ '+' '.join(map(str,argv))+'\n');out.flush()
        proc=subprocess.run(list(map(str,argv)),cwd=cwd,stdout=out,stderr=subprocess.STDOUT,timeout=timeout)
    append(run_dir()/'preparation/commands.jsonl',dict(argv=list(map(str,argv)),cwd=str(cwd),returncode=proc.returncode,
        elapsed_seconds=time.time()-began,log=str(path)))
    if proc.returncode:raise RuntimeError(f'exit {proc.returncode}; see {path}')

def restore(env):
    from pathlib import Path
    repo=Path(env['project']);path=run_dir()/'preparation'/f"{env['id']}.log"
    if not (repo/'.git').exists():
        repo.mkdir(parents=True,exist_ok=True)
        command(['git','init'],repo,path);command(['git','remote','add','origin',env['url']],repo,path)
        command(['git','fetch','--depth','1','origin',env['commit']],repo,path)
        command(['git','checkout','--detach',env['commit']],repo,path)
    # IDE background fetches can replace FETCH_HEAD; always check out the pinned SHA.
    if subprocess.run(['git','rev-parse','--verify','HEAD'],cwd=repo,capture_output=True).returncode:
        command(['git','checkout','--detach',env['commit']],repo,path)
    assert git(repo,'rev-parse','HEAD')==env['commit']
    tc=(repo/'lean-toolchain').read_text().strip();assert tc.endswith(':'+env['version'])
    # Collect applicable repository instructions for the human/agent audit before building.
    instructions={str(p.relative_to(repo)):p.read_text() for p in repo.rglob('AGENTS.md') if '.lake' not in p.parts and '.git' not in p.parts}
    write(run_dir()/'preparation'/f"{env['id']}_instructions.json",instructions)
    command(['elan','toolchain','install',tc],HERE,path)
    manifest=read(repo/'lake-manifest.json')
    for dep in manifest.get('packages',[]):
        if dep['type']!='git':raise RuntimeError('unpinned non-git dependency')
        dest=repo/manifest.get('packagesDir','.lake/packages')/dep['name'].strip('«»')
        if not (dest/'.git').exists():
            dest.mkdir(parents=True,exist_ok=True);command(['git','init'],dest,path)
            command(['git','remote','add','origin',dep['url']],dest,path)
            command(['git','fetch','--depth','1','origin',dep['rev']],dest,path)
            command(['git','checkout','--detach',dep['rev']],dest,path)
        assert git(dest,'rev-parse','HEAD')==dep['rev']
        tag=dep.get('inputRev','')
        if dep['name'].strip('«»')=='proofwidgets' and tag.startswith('v'):
            if subprocess.run(['git','rev-parse','--verify','refs/tags/'+tag],cwd=dest,capture_output=True).returncode:
                command(['git','fetch','--depth','1','origin','tag',tag],dest,path)
    result=dict(**env,toolchain=tc,restored=True)
    write(run_dir()/'preparation'/f"{env['id']}_restored.json",result);return result

def build(env):
    from pathlib import Path
    repo=Path(env['project']);tc=(repo/'lean-toolchain').read_text().strip()
    path=run_dir()/'preparation'/f"{env['id']}_build.log"
    for p in repo.rglob('README.md'):
        if '.git' not in p.parts and '.lake' not in p.parts:p.read_text()
    modules=set();data=rows()
    for p in env['problems']:
        row=data[p-1];text=(repo/row['file_path']).read_text() if row['file_path'] else row['header']
        modules.update(source_imports(text))
    targets=old.imports(repo,modules);prefix=['elan','run',tc,'lake']
    manifest=read(repo/'lake-manifest.json')
    has_mathlib=(repo/'Mathlib').is_dir() or any(d['name'].strip('«»')=='mathlib' for d in manifest.get('packages',[]))
    if targets and has_mathlib:command(prefix+['exe','cache','get',*targets],repo,path)
    targets=[m for m in sorted(modules) if m.split('.')[0] not in {'Init','Lean','Std','Lake'}]
    command(prefix+['build',*targets],repo,path)
    result=dict(**env,toolchain=tc,ready=True,imports=sorted(modules))
    write(run_dir()/'preparation'/f"{env['id']}_ready.json",result);log('environment_ready',id=env['id']);return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('phase',choices=['inventory','restore','build']);parser.add_argument('--env');parser.add_argument('--workers',type=int,default=2)
    args=parser.parse_args();envs=inventory();write(run_dir()/'environment_manifest.json',list(envs.values()))
    selected=[envs[args.env]] if args.env else list(envs.values())
    if args.phase!='inventory':
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures={pool.submit(restore if args.phase=='restore' else build,e):e['id'] for e in selected if not (run_dir()/'preparation'/f"{e['id']}_{'restored' if args.phase=='restore' else 'ready'}.json").exists()}
            for future in as_completed(futures):
                try:future.result()
                except Exception as exc:
                    log('environment_failure',id=futures[future],error=str(exc));write(run_dir()/'preparation'/f"{futures[future]}_{args.phase}_failure.json",dict(error=str(exc)))
