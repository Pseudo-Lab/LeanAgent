"""Sequential environment preparation; only newly created scratch is reclaimed."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=Path(os.environ.get('LEAN_ARENA_WORKSPACE', next((str(p) for p in HERE.parents if (p/'refactor_arena').is_dir()), str(HERE))))
ROWS=[json.loads(l) for l in (HERE/'warmup.jsonl').read_text().splitlines()]
SCRATCH=HERE/'scratch'
LAKE=str(Path.home()/'.elan/bin/lake')
ELAN=str(Path.home()/'.elan/bin/elan')


def call(cmd,cwd,env,path):
    path.parent.mkdir(parents=True,exist_ok=True)
    print('RUN',*cmd,flush=True)
    t=time.time()
    with path.open('w') as f:
        p=subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT)
    print('EXIT',p.returncode,'seconds',round(time.time()-t),path,flush=True)
    if p.returncode:raise RuntimeError('Command failed; see '+str(path))


def main():
    jobs={}
    for i,r in enumerate(ROWS,1):
        for e in r['version_info']:
            for ver,pin in e.items():jobs.setdefault((r['source'],ver,pin),[]).append(i)
    # A shared environment can be primary for P1/P2 but secondary for P3.
    # Topological order by per-problem primary dependencies avoids empty pools.
    pending=dict(jobs);ordered=[];finished=set()
    while pending:
        before=len(pending)
        for key,ids in list(pending.items()):
            needs=set()
            for i in ids:
                r=ROWS[i-1];pv=next(iter(r['version_info'][0]));pc=r['version_info'][0][pv]
                primary=(r['source'],pv,pc)
                if primary!=key:needs.add(primary)
            if needs<=finished:
                ordered.append((key,ids));finished.add(key);del pending[key]
        if len(pending)==before:
            raise RuntimeError('Cyclic environment dependencies')
    for (source,ver,pin),ids in ordered:
        if len(sys.argv)>1 and source not in sys.argv[1:]:continue
        if all((HERE/'runs'/f'{i:02d}'/ver/'result.json').exists() for i in ids):continue
        log=HERE/'setup_logs'/f'{source}_{ver}';log.mkdir(parents=True,exist_ok=True)
        env=dict(os.environ)
        if source=='strata' and ver=='v4.26.0' and (ROOT/'refactor_arena/strata/.git').exists():
            project=ROOT/'refactor_arena/strata'
            call([sys.executable,str(HERE/'minimize.py'),str(project),ver,*map(str,ids)],HERE,env,log/'run.log')
            continue
        scratch=SCRATCH/f'{source}_{ver}';scratch.mkdir(parents=True,exist_ok=True)
        project=scratch/'project'
        env['XDG_CACHE_HOME']=str(scratch/'cache')
        if ver!='v4.26.0':
            env['ELAN_HOME']=str(scratch/'elan');env['MIN_ELAN_HOME']=env['ELAN_HOME']
        if not project.exists():
            old=ROOT/'refactor_arena/prompt_sweep_2026_10_15/environments'/source
            if old.is_dir():
                call(['git','clone','--shared',str(old),str(project)],HERE,env,log/'clone.log')
            else:
                url=ROWS[ids[0]-1]['url'] or 'https://github.com/leanprover-community/mathlib4.git'
                call(['git','clone','--filter=blob:none','--no-checkout',url,str(project)],HERE,env,log/'clone.log')
        if subprocess.run(['git','cat-file','-e',pin+'^{commit}'],cwd=project,capture_output=True).returncode:
            url=ROWS[ids[0]-1]['url'] or 'https://github.com/leanprover-community/mathlib4.git'
            call(['git','fetch','--depth','1',url,pin],project,env,log/'fetch.log')
        call(['git','checkout','--detach',pin],project,env,log/'checkout.log')
        if ver!='v4.26.0':call([ELAN,'toolchain','install','leanprover/lean4:'+ver],project,env,log/'toolchain.log')
        if source!='strata':call([LAKE,'exe','cache','get'],project,env,log/'cache.log')
        if source!='putnambench':
            targets=sorted({ROWS[i-1]['file_path'][:-5].replace('/','.') for i in ids})
            call([LAKE,'build',*targets],project,env,log/'build.log')
        call([sys.executable,str(HERE/'minimize.py'),str(project),ver,*map(str,ids)],HERE,env,log/'run.log')
        # Explicit user authorization: remove only this run's scratch environment.
        shutil.rmtree(scratch)
        print('CLEANED',scratch,'free GiB',round(shutil.disk_usage(HERE).free/2**30,2),flush=True)

if __name__=='__main__':main()
