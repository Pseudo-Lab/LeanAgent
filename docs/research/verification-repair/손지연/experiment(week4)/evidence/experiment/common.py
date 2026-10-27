"""Experiment-local utilities; the reusable verifier package is read only."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE.parent / 'verification-repair'))

def sha(value):
    return hashlib.sha256(value.encode() if isinstance(value, str) else value).hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def write(path, value):
    path = Path(path); path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + f'.{os.getpid()}.{time.time_ns()}.tmp')
    tmp.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    tmp.replace(path)

def append(path, value):
    path = Path(path); path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a') as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        stream.write(json.dumps(value, ensure_ascii=False) + '\n'); stream.flush()
        fcntl.flock(stream, fcntl.LOCK_UN)

def rows():
    return [json.loads(line) for line in (HERE/'benchmark_data_warmup.jsonl').read_text().splitlines()]

def run_dir():
    return HERE/(HERE/'LATEST_RUN').read_text().strip()

def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args], text=True).strip()

def package_hashes():
    return {str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in sorted((HERE.parent/'verification-repair/lean_repair').glob('*')) if p.is_file()}

def log(event, **data):
    print(json.dumps(dict(event=event, **data), ensure_ascii=False), flush=True)
