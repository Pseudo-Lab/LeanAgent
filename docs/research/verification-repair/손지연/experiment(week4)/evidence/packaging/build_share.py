"""Copy the two authorized source trees; never write into either source."""
import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys

HERE = Path(__file__).resolve().parent
SHARE = HERE.parents[6]
WORKSPACE = SHARE.parent
WARMUP = SHARE/'docs/research/refactoring/warmup/손지연'
IMPLEMENTATION = SHARE/'docs/research/verifier-guided-agent/손지연'
SOURCES = [('week4/experiment', WARMUP/'evidence/experiment'),
           ('week4/verification-repair', IMPLEMENTATION/'evidence/verification-repair')]
EXCLUDED = {'envs', '__pycache__', '.matplotlib', '.DS_Store'}

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''): h.update(block)
    return h.hexdigest()

def jobs():
    for source, target in SOURCES:
        root = WORKSPACE/source
        for folder, dirs, files in os.walk(root):
            dirs[:] = sorted(d for d in dirs if d not in EXCLUDED)
            for name in sorted(files):
                if name in EXCLUDED: continue
                p = Path(folder)/name
                if p.is_symlink(): raise RuntimeError(f'Review symlink: {p}')
                yield p, target/p.relative_to(root)

def clone(source, dest):
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists():
        if sha(dest) != sha(source): raise RuntimeError(f'Destination changed: {dest}')
        return 'existing'
    cloned = False
    if sys.platform == 'darwin':
        libc = ctypes.CDLL('/usr/lib/libSystem.B.dylib', use_errno=True)
        libc.clonefile.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_int]
        cloned = libc.clonefile(os.fsencode(source), os.fsencode(dest), 0) == 0
    if not cloned: shutil.copyfile(source, dest)
    shutil.copystat(source, dest)
    if source.stat().st_ino == dest.stat().st_ino: raise RuntimeError('No hard links')
    return 'apfs_clone' if cloned else 'copy'

def metadata(path):
    s = path.stat()
    return dict(size=s.st_size, mode=s.st_mode, inode=s.st_ino, mtime_ns=s.st_mtime_ns)

def copy():
    pairs = list(jobs()); manifest = HERE/'copy-manifest.jsonl'
    if manifest.exists(): raise SystemExit('Copy already recorded. Use --verify instead of replacing provenance.')
    total = 0
    with manifest.open('w') as stream:
        for n, (source, dest) in enumerate(pairs, 1):
            before = metadata(source); digest = sha(source); method = clone(source, dest)
            if sha(dest) != digest or metadata(source) != before: raise RuntimeError(f'Copy mismatch: {source}')
            stream.write(json.dumps(dict(source=str(source.relative_to(WORKSPACE)),
                destination=str(dest.relative_to(SHARE)), sha256=digest, method=method, original_metadata=before), ensure_ascii=False)+'\n')
            total += before['size']
            if n % 10000 == 0: print(json.dumps(dict(copied=n, planned=len(pairs))), flush=True)
    print(json.dumps(dict(copied=len(pairs), bytes=total)), flush=True)

def verify(check_source=True):
    differences = []; count = 0; total = 0; counts = {}
    with (HERE/'copy-manifest.jsonl').open() as stream:
        for line in stream:
            row = json.loads(line); source = WORKSPACE/row['source']; dest = SHARE/row['destination']
            count += 1; total += row['original_metadata']['size']
            counts[row['source'].split('/')[1]] = counts.get(row['source'].split('/')[1], 0)+1
            if check_source and sha(source) != row['sha256']: differences.append(dict(path=row['source'], kind='source_sha256'))
            if check_source and metadata(source) != row['original_metadata']: differences.append(dict(path=row['source'], kind='source_metadata'))
            if sha(dest) != row['sha256']: differences.append(dict(path=row['destination'], kind='destination_sha256'))
            if check_source and source.stat().st_ino == dest.stat().st_ino: differences.append(dict(path=row['destination'], kind='hard_link'))
    expected = {json.loads(line)['source'] for line in (HERE/'copy-manifest.jsonl').read_text().splitlines()}
    if check_source:
        present = {str(p.relative_to(WORKSPACE)) for p,_ in jobs()}
        if present != expected: differences.append(dict(kind='source_file_set_changed', added=sorted(present-expected), removed=sorted(expected-present)))
    result = dict(passed=not differences, files=count, bytes=total, files_by_source=counts,
        original_payloads_unchanged=not any(x['kind'].startswith('source') for x in differences) if check_source else None, differences=differences,
        excluded_regenerable=sorted(EXCLUDED),
        scope='Every included source file: SHA-256 plus mode/size/inode/mtime; excluded environment caches are not audited or modified. No original tree writes.')
    (HERE/('preservation.json' if check_source else 'copy-integrity.json')).write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(result,ensure_ascii=False))
    if differences: raise SystemExit(1)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__); group=parser.add_mutually_exclusive_group()
    group.add_argument('--verify', action='store_true');group.add_argument('--verify-copy', action='store_true')
    args=parser.parse_args()
    if args.verify or args.verify_copy: verify(check_source=args.verify)
    else: copy()
