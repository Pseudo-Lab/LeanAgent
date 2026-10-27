"""Generate the bounded warmup edits and verify them with frozen existing checkers.

No model API calls. A prepared, clean, pinned Lean project and the recorded Arena
checkout are explicit inputs. This is a replay adapter, not a new proof checker.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys

HERE = Path(__file__).resolve().parent
IDENTITY = json.loads((HERE / 'verifier-identity.json').read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def inputs():
    for filename, expected in [('benchmark.jsonl', IDENTITY['benchmarkSha256']),
                               ('starting-selection.json', IDENTITY['startingSha256'])]:
        if sha((HERE / filename).read_bytes()) != expected:
            raise ValueError(f'Frozen input changed: {filename}')
    return ([json.loads(l) for l in (HERE / 'benchmark.jsonl').read_text().splitlines()],
            json.loads((HERE / 'starting-selection.json').read_text()))


def generate(output):
    _, snapshot = inputs()
    output.mkdir(parents=True, exist_ok=False)
    groups = {}
    for script in sorted((HERE / 'generators').glob('*.py')):
        dest = output / script.stem
        subprocess.run([sys.executable, str(script), '--baseline', str(HERE / 'starting-selection.json'),
                        '--output', str(dest)], check=True)
        for proof in sorted(dest.glob('P*/*.lean')):
            problem = int(proof.parent.name[1:])
            row = snapshot['problems'][problem - 1]
            code = proof.read_text()
            if sha(code.encode()) == row['candidateHash'] or proof.stem in {'original', 'current', 'starting'}:
                continue
            group = groups.setdefault(str(problem), [])
            digest = sha(code.encode())
            if digest in {c['candidateHash'] for c in group}:
                continue
            group.append({'id': proof.stem, 'proof': code, 'candidateHash': digest,
                          'generatedPath': str(proof.relative_to(output))})
    if set(groups) != {str(i) for i in range(1, 16)}:
        raise ValueError('New distinct candidates must cover all 15 problems')
    write(output / 'candidates.json', {'schemaVersion': 1,
        'startingSnapshotSha256': IDENTITY['startingSha256'], 'problems': groups})
    print(json.dumps({p: len(cs) for p, cs in groups.items()}, sort_keys=True))


def git(project, *args):
    return subprocess.check_output(['git', '-C', str(project), *args], text=True).strip()


def clean_project(project, revision, version):
    if git(project, 'rev-parse', 'HEAD') != revision or git(project, 'diff', 'HEAD', '--', '.'):
        raise ValueError('Source revision/cleanliness differs from the benchmark pin')
    if (project / 'lean-toolchain').read_text().strip() != f'leanprover/lean4:{version}':
        raise ValueError('Toolchain pin mismatch')
    manifest = (project / 'lake-manifest.json').read_bytes()
    for package in json.loads(manifest)['packages']:
        if package['type'] != 'git':
            raise ValueError('Unpinned dependency type')
        dep = project / '.lake/packages' / package['name'].strip('«»')
        if git(dep, 'rev-parse', 'HEAD') != package['rev'] or git(dep, 'diff', 'HEAD', '--', '.'):
            raise ValueError(f'Dependency revision/cleanliness mismatch: {package["name"]}')
    return sha(manifest)


def load_checkers(arena, runtime):
    for filename, expected in IDENTITY['files'].items():
        if sha((arena / filename).read_bytes()) != expected:
            raise ValueError(f'Checker adapter changed: {filename}')
    for name in ('__init__.py', 'lean.py', 'tokens.py'):
        dest = runtime / 'refactor_eval' / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(subprocess.check_output(['git', '-C', str(arena), 'show',
            f'{IDENTITY["evaluatorRevision"]}:refactor_eval/{name}']))
    sys.path[:0] = [str(runtime), str(arena / 'scripts')]
    return (importlib.import_module('refactor_eval.lean'),
            importlib.import_module('refactor_eval.tokens'),
            importlib.import_module('verify_warmup_pins'),
            importlib.import_module('verify_p12_pins'))


def verify(args):
    rows, snapshot = inputs()
    meta = rows[args.problem - 1]
    row = snapshot['problems'][args.problem - 1]
    pins = {v: r for pin in meta['version_info'] for v, r in pin.items()}
    revision = pins[args.version]
    project, arena, output = args.project.resolve(), args.arena.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    report = {'problem': args.problem, 'version': args.version, 'revision': revision,
              'repetitions': args.runs, 'status': 'preparing', 'candidates': {}}
    try:
        manifest_hash = clean_project(project, revision, args.version)
        lean, tokens, common, p12 = load_checkers(arena, output / 'runtime')
        selection = next(c for c in row['teamResults'] if c['id'] == row['selectedCandidateId'])
        if sha(selection['proof'].encode()) != row['candidateHash']:
            raise ValueError('Starting proof hash mismatch')
        candidates = json.loads(args.candidates.read_text())
        if candidates['startingSnapshotSha256'] != IDENTITY['startingSha256']:
            raise ValueError('Candidate input uses a different starting selection')
        trials = [('original', meta['src']), ('starting', selection['proof'])]
        seen = {'original', 'starting'}
        for c in candidates['problems'][str(args.problem)]:
            if sha(c['proof'].encode()) != c['candidateHash']:
                raise ValueError('Candidate bytes differ from recorded hash')
            if args.candidate and c['id'] not in args.candidate:
                continue
            if c['id'] in seen or '/' in c['id'] or '\\' in c['id'] or c['id'] in {'.', '..'}:
                raise ValueError('Unsafe/duplicate candidate label')
            seen.add(c['id']); trials.append((c['id'], c['proof']))
        if args.candidate and not set(args.candidate) <= seen:
            raise ValueError('Requested candidate was not generated')
        source = (project / meta['file_path']).read_text() if meta['file_path'] else meta['header'] + meta['src']
        context, lead = common.template(meta, source)
        env = {'id': args.version, 'project': str(project), 'toolchain': f'leanprover/lean4:{args.version}',
               'command': ['lake', 'env', 'lean', '-j1', f'-M{args.memory_mb}']
                          + ([] if args.problem == 12 else ['-T200000']),
               'template': context, 'timeout_seconds': 180}
        evaluator = lean.LeanEvaluator()
        report.update(sourceSha256=sha(source.encode()), manifestSha256=manifest_hash,
                      fingerprint=evaluator.fingerprint(env), status='verifying',
                      protocol=p12.PROTOCOL if args.problem == 12 else 'frozen PR3',
                      countsInCommonScore=args.problem != 12)
        expected_context = None
        for label, code in trials:
            dest = output / label
            if args.problem != 12:
                result = evaluator.evaluate(lead + code, {'statement': lead + meta['statement'],
                    'name': meta['name']}, [env], dest, args.runs)
                report['candidates'][label] = {'sha256': sha(code.encode()), 'result': result}
            else:
                dest.mkdir()
                candidate = dest / 'proof.lean'; candidate.write_text(code)
                statement = dest / 'statement.lean'; statement.write_text(meta['statement'])
                item = {'sha256': sha(code.encode()), 'tokens': p12.gate(code, meta['statement'], tokens),
                        'runs': [], 'valid': False}
                start = source.index(meta['src']); first = source[:start].count('\n') + 1
                last = first + len(meta['src'].splitlines()) - 1
                for n in range(1, args.runs + 1):
                    tag = f'repeat-{n}'
                    command = [sys.executable, str(arena / 'scripts/p12_fullsource_verifier.py'),
                        '--repo', str(project), '--file', meta['file_path'], '--start', str(first),
                        '--end', str(last), '--name', meta['name'], '--statement', str(statement),
                        '--candidate', str(candidate), '--workdir', str(dest), '--tag', tag,
                        '--extra-import', 'Mathlib.Util.CountHeartbeats', '--lean-arg=-j1',
                        f'--lean-arg=-M{args.memory_mb}', '--timeout', '180']
                    run = subprocess.run(command, capture_output=True, text=True,
                                         env=dict(os.environ, LEAN_NUM_THREADS='1'))
                    (dest / f'{tag}.driver.log').write_text(run.stdout + run.stderr)
                    measured = json.loads((dest / f'{tag}.result.json').read_text())
                    valid = p12.audit_run(measured, meta['name'], run.returncode)
                    hashes = p12.context_hashes(dest, tag, code)
                    if expected_context is None: expected_context = hashes
                    if hashes != expected_context: raise ValueError('Whole-file context changed')
                    measured['contextHashes'] = hashes
                    item['runs'].append(measured)
                    if not valid: break
                item['valid'] = len(item['runs']) == args.runs and all(r['valid'] for r in item['runs'])
                if item['valid']:
                    item['medianHeartbeats'] = statistics.median(r['heartbeat']['heartbeats'] for r in item['runs'])
                report['candidates'][label] = item
            write(output / 'result.json', report)
            item = report['candidates'][label]
            if label in {'original', 'starting'} and not item.get('result', item)['valid']:
                report.update(status='control_failed', controlsValid=False)
                return
        if clean_project(project, revision, args.version) != manifest_hash:
            raise ValueError('Environment changed during measurement')
        report['controlsValid'] = all(
            (report['candidates'][label].get('result', report['candidates'][label]))['valid']
            for label in ('original', 'starting'))
        report['status'] = 'completed'
    except KeyboardInterrupt:
        report.update(status='interrupted', controlsValid=False)
        raise
    except Exception as error:
        report.update(status='environment_or_protocol_failed', error=str(error))
        raise
    finally:
        write(output / 'result.json', report)
    # Completion is not evidence that every candidate passed. See individual results.


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    g = sub.add_parser('generate'); g.add_argument('--output', type=Path, required=True)
    v = sub.add_parser('verify')
    for name in ('arena', 'project', 'candidates', 'output'):
        v.add_argument('--' + name, type=Path, required=True)
    v.add_argument('--problem', type=int, choices=range(1, 16), required=True)
    v.add_argument('--version', required=True)
    v.add_argument('--candidate', action='append')
    v.add_argument('--runs', type=int, choices=(1, 3), default=3)
    v.add_argument('--memory-mb', type=int, choices=(6144, 8192), default=6144)
    args = parser.parse_args()
    if args.command == 'generate': generate(args.output.resolve())
    else: verify(args)


if __name__ == '__main__': main()
