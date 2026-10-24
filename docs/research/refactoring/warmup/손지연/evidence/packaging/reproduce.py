"""Replay frozen histories from saved records; no model, Lean or network calls."""
import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import shutil
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
EXPERIMENT = HERE.parent/'experiment'
RUN_RELATIVE = Path((EXPERIMENT/'LATEST_RUN').read_text().strip())

def sha(value):
    return hashlib.sha256(value.encode() if isinstance(value,str) else value).hexdigest()

def read(path): return json.loads(path.read_text())

def extract(path, names, namespace):
    """Compile only named constants/pure reducers, leaving runner imports unused."""
    tree = ast.parse(path.read_text())
    nodes = []
    for node in tree.body:
        targets = {node.name} if isinstance(node, ast.FunctionDef) else {
            target.id for target in node.targets if isinstance(target,ast.Name)
        } if isinstance(node,ast.Assign) else set()
        if targets & names: nodes.append(node)
    found = {node.name for node in nodes if isinstance(node,ast.FunctionDef)}
    found |= {target.id for node in nodes if isinstance(node,ast.Assign) for target in node.targets if isinstance(target,ast.Name)}
    if not names <= found: raise RuntimeError(f'Missing recorded source: {names-found}')
    exec(compile(ast.Module(body=nodes,type_ignores=[]),str(path),'exec'),namespace)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='Write a new JSON outside the archived evidence directory')
    args = parser.parse_args()
    if RUN_RELATIVE.is_absolute() or '..' in RUN_RELATIVE.parts:
        raise ValueError('Invalid archived run path')
    temporary = tempfile.TemporaryDirectory(prefix='leanagent-week4-replay-')
    root = Path(temporary.name)
    with tarfile.open(EXPERIMENT/'records.tar.gz', 'r:gz') as archive:
        for member in archive:
            target = root/member.name
            if not member.isfile() or not target.resolve().is_relative_to(root.resolve()):
                raise ValueError(f'Unsafe archive entry: {member.name}')
            target.parent.mkdir(parents=True, exist_ok=True)
            with archive.extractfile(member) as source, target.open('wb') as output:
                shutil.copyfileobj(source, output)
    RUN = root/RUN_RELATIVE
    for result in (EXPERIMENT/RUN_RELATIVE/'runs').glob('*/*/*/*/*/result.json'):
        destination = RUN/'runs'/result.parent.relative_to(EXPERIMENT/RUN_RELATIVE/'runs')
        shutil.copytree(result.parent, destination, dirs_exist_ok=True)
    namespace = dict(Path=Path,Counter=Counter,json=json,re=re,read=read,sha=sha)
    extract(EXPERIMENT/'subscription.py',{'redact'},namespace)
    extract(EXPERIMENT/'engine.py',{'INFRA','CONSTRAINTS','rank','choose','make_request','initial_state','update_state'},namespace)
    extract(EXPERIMENT/'audit.py',{'INITIAL_ENGINE'},namespace)
    extract(EXPERIMENT/'replay.py',{'replay'},namespace)
    values = [namespace['replay'](path.parent) for path in sorted((RUN/'runs').glob('*/*/*/*/*/result.json'))]
    for value in values: value['path']=str(Path(value['path']).relative_to(RUN))
    result = dict(histories=len(values),matched=sum(v['match'] for v in values),
        new_model_calls=0,new_lean_calls=0,source='Original archived pure functions; no original module initialization.',
        items=values)
    if args.output:
        if args.output.resolve().is_relative_to(HERE.parent.resolve()):
            raise ValueError('Write new replay results outside the archived evidence directory')
        args.output.resolve().parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    temporary.cleanup()
    print(json.dumps({k:v for k,v in result.items() if k!='items'}))
    if result['histories']!=360 or result['matched']!=360: raise SystemExit(1)

if __name__=='__main__': main()
