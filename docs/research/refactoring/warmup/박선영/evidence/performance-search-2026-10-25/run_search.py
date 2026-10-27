#!/usr/bin/env python3
"""Isolated, bounded performance search; no automatic repair, build or submission."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import statistics
import sys
import tempfile

HERE = Path(__file__).resolve().parent
EVIDENCE = HERE.parent
OUTPUT = EVIDENCE / 'metrics' / HERE.name
spec = importlib.util.spec_from_file_location('performance_evaluator', EVIDENCE / 'run_experiments.py')
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def read(path):
    return json.loads(path.read_text(encoding='utf-8'))


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x', encoding='utf-8') as stream:
        stream.write(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def copy_new(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open('xb') as stream:
        stream.write(source.read_bytes())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def body_hash(path):
    return base.digest(path.read_text(encoding='utf-8').rstrip('\n'))


@contextmanager
def lock():
    OUTPUT.mkdir(parents=True, exist_ok=True)
    path = OUTPUT / '.lock'
    with path.open('x') as stream:
        stream.write(str(os.getpid()))
    try:
        yield
    finally:
        path.unlink()


def folder(problem):
    if problem not in (8, 11):
        raise ValueError('Only P8/P11 are supported')
    return OUTPUT / f'P{problem}'


def fingerprint(repo, row):
    version, revision = base.validate_environment(repo, row)
    files = [Path(__file__), EVIDENCE / 'run_experiments.py', EVIDENCE / 'benchmark.jsonl',
             base.SHARED / 'proof_tokens.py', base.SHARED / 'verify_candidate.py',
             repo / 'lean-toolchain', repo / 'lake-manifest.json', repo / row['file_path']]
    toolchain = (repo / 'lean-toolchain').read_text().strip().replace('/', '--').replace(':', '---')
    installed = Path.home() / '.elan/toolchains' / toolchain / 'bin'
    # Require the existing pinned installation; never let this adapter install one.
    files.extend([installed / 'lean', installed / 'lake',
                  repo / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Util/CountHeartbeats.olean'])
    return {'version': version, 'revision': revision,
            'files': {str(path.resolve()): sha(path) for path in files}}


def contract(path, row):
    text = path.read_text(encoding='utf-8').rstrip('\n')
    forbidden = base.validate_candidate(text, row['statement'])
    if forbidden:
        raise ValueError(f'Forbidden patterns: {forbidden}')
    return text


def initialize(problem, repo, start):
    target = folder(problem)
    if target.exists():
        raise ValueError('Session already exists; choose a new experiment instead of overwriting')
    row = base.problem(problem)
    repo, start = repo.resolve(), start.resolve()
    frozen = fingerprint(repo, row)
    contract(start, row)
    original = row['src'].rstrip('\n')
    base.splice((repo / row['file_path']).read_text(), original, original)
    target.mkdir()
    reference = target / 'reference.lean'
    with reference.open('x', encoding='utf-8') as stream:
        stream.write(original + '\n')
    copy_new(start, target / 'start.lean')
    write(target / 'session.json', {'problem': problem, 'created_at': base.stamp(),
        'repo': str(repo), 'start_source': str(start), 'start_source_sha256': sha(start),
        'fingerprint': frozen, 'budget': 6, 'timeout': 180,
        'controls': {name: sha(target / f'{name}.lean') for name in ('reference', 'start')},
        'scope': 'One pinned local version; no official score or automatic adoption.'})


def unchanged(target, session):
    if fingerprint(Path(session['repo']), base.problem(session['problem'])) != session['fingerprint']:
        raise ValueError('Environment/evaluator fingerprint drift; stop this session')
    for name, expected in session['controls'].items():
        if sha(target / f'{name}.lean') != expected:
            raise ValueError('Frozen control changed')
    for record in (target / 'candidates').glob('*/registration.json'):
        item = read(record)
        for filename, expected in item['files'].items():
            if sha(record.parent / filename) != expected:
                raise ValueError('Frozen candidate/hypothesis changed')


def register(problem, candidate, hypothesis):
    target = folder(problem)
    session = read(target / 'session.json')
    unchanged(target, session)
    records = sorted((target / 'candidates').glob('*/registration.json'))
    # Reserved directories count too, so interrupted registrations never refund budget.
    used = list((target / 'candidates').glob('c*'))
    if len(used) >= session['budget']:
        raise ValueError('Candidate budget exhausted')
    candidate, hypothesis = candidate.resolve(), hypothesis.resolve()
    row = base.problem(problem)
    text = contract(candidate, row)
    proposal = read(hypothesis)
    if str(proposal['problem']) not in (str(problem), f'P{problem}'):
        raise ValueError('Hypothesis problem mismatch')
    if not proposal.get('strategy') or not proposal.get('rationale'):
        raise ValueError('Prewritten strategy and rationale required')
    parent = Path(proposal['parent']['path']).resolve()
    if sha(parent) != proposal['parent']['sha256']:
        raise ValueError('Parent hash mismatch (exact file bytes required)')
    accepted_parents = {body_hash(target / 'start.lean'), body_hash(target / 'reference.lean')}
    accepted_parents.update(read(record)['body_sha256'] for record in records)
    if body_hash(parent) not in accepted_parents:
        raise ValueError('Parent is not a control or registered candidate')
    if base.digest(text) in accepted_parents:
        raise ValueError('Duplicate normalized proof body')
    name = f'c{len(used) + 1:03d}'
    dest = target / 'candidates' / name
    dest.mkdir(parents=True, exist_ok=False)
    copy_new(candidate, dest / 'candidate.lean')
    copy_new(hypothesis, dest / 'hypothesis.json')
    copy_new(parent, dest / 'parent.lean')
    write(dest / 'registration.json', {'id': name, 'registered_at': base.stamp(),
        'source': str(candidate), 'hypothesis_source': str(hypothesis),
        'body_sha256': base.digest(text), 'proof_tokens': base.tokens.proof_length(text, row['statement']),
        'files': {f: sha(dest / f) for f in ('candidate.lean', 'hypothesis.json', 'parent.lean')}})
    return name


def accepted(target, name, repetition=1):
    path = target / 'runs' / f'{name}-{repetition}' / 'review.json'
    return path.is_file() and read(path)['status'] == 'passed'


def classify(result, log, reference_axioms):
    if result['status'] == 'timeout':
        return 'timeout'
    if not result['valid']:
        if any(pattern in log for pattern in ('does not exist', 'unknown module prefix', 'failed to open file')):
            return 'environment_error'
        return 'compile_or_validation_failed'
    if not set(result['axioms']) <= set(reference_axioms):
        return 'new_axioms'
    if result['status'] != 'passed' or result['heartbeat'] is None:
        return 'measurement_failed'
    return 'passed'


def run(problem, name, repetition):
    if name not in ('reference', 'start') and not re.fullmatch(r'c00[1-6]', name):
        raise ValueError('Invalid run name')
    if repetition not in (1, 2, 3):
        raise ValueError('Repetition must be 1, 2 or 3')
    target = folder(problem)
    session = read(target / 'session.json')
    if (target / 'STOP.json').exists():
        raise ValueError('Theorem stopped; inspect STOP.json, do not retry in this session')
    # A failed or interrupted original stops all further runs, not just candidates.
    for prior in (target / 'runs').glob('reference-*'):
        if not (prior / 'review.json').is_file() or read(prior / 'review.json')['status'] != 'passed':
            raise ValueError('Original failed or interrupted; theorem stopped')
    if name != 'reference' and not accepted(target, 'reference'):
        raise ValueError('Fresh original must pass first')
    if name not in ('reference', 'start') and not accepted(target, 'start'):
        raise ValueError('Fresh starting best must pass first')
    if repetition > 1 and not accepted(target, name, repetition - 1):
        raise ValueError('Previous repetition must pass first')
    candidate = (target / f'{name}.lean' if name in ('reference', 'start')
                 else target / 'candidates' / name / 'candidate.lean')
    if name.startswith('c'):
        read(candidate.parent / 'registration.json')
    output = target / 'runs' / f'{name}-{repetition}'
    output.mkdir(parents=True, exist_ok=False)
    write(output / 'started.json', {'started_at': base.stamp(), 'name': name, 'repetition': repetition})
    status = 'preflight_error'
    review = {'name': name, 'repetition': repetition, 'status': status, 'raw_result': None}
    try:
        unchanged(target, session)
        contract(candidate, base.problem(problem))
        args = argparse.Namespace(problem=problem, repo=Path(session['repo']), candidate=candidate,
            label=name, hypothesis=f'{name}; frozen registration/control', timeout=session['timeout'])
        status = 'tool_error'
        result = base.evaluate(args, output_dir=output / 'raw')
        if read(output / 'raw/result.json') != result:
            raise RuntimeError('Returned result differs from saved raw evidence')
        review['raw_result'] = str(output / 'raw/result.json')
        # Do not modify raw evaluator output; this verdict is a separate audit.
        if name == 'reference':
            reference_axioms = result['axioms'] or []
        else:
            reference_axioms = read(target / 'runs/reference-1/raw/result.json')['axioms']
        status = classify(result, (output / 'raw/check.log').read_text(), reference_axioms)
        review.update({'status': status, 'heartbeat': result['heartbeat'],
                       'proof_tokens': result['proof_tokens'], 'axioms': result['axioms']})
        status = 'fingerprint_or_input_drift'
        unchanged(target, session)
    except Exception as exc:
        review.update({'status': status, 'error': f'{type(exc).__name__}: {exc}'})
    write(output / 'review.json', review)
    if review['status'] in ('preflight_error', 'fingerprint_or_input_drift', 'environment_error', 'tool_error') or (name == 'reference' and review['status'] != 'passed'):
        write(target / 'STOP.json', {'at': base.stamp(), 'run': str(output), 'reason': review['status']})
    return review


def summarize(problem):
    target = folder(problem)
    session = read(target / 'session.json')
    unchanged(target, session)
    groups = {}
    for path in sorted((target / 'runs').glob('*/review.json')):
        review = read(path)
        groups.setdefault(review['name'], []).append(review)
    summaries = {}
    for name, reviews in groups.items():
        values = [r['heartbeat'] for r in reviews if r['status'] == 'passed']
        complete = len(reviews) == 3 and len(values) == 3
        summaries[name] = {'runs': reviews, 'confirmed_three_runs': complete,
                           'median_heartbeat': statistics.median(values) if complete else None,
                           'range_heartbeat': [min(values), max(values)] if complete else None,
                           'proof_tokens': reviews[0].get('proof_tokens')}
    for name, item in summaries.items():
        for control in ('reference', 'start'):
            reference = summaries.get(control, {})
            item[f'heartbeat_reduction_vs_{control}_pct'] = base.reduction(
                reference.get('median_heartbeat'), item['median_heartbeat'])
            item[f'token_reduction_vs_{control}_pct'] = base.reduction(
                reference.get('proof_tokens'), item['proof_tokens']) if item['confirmed_three_runs'] and reference.get('confirmed_three_runs') else None
    return {'problem': problem, 'generated_at': base.stamp(), 'official_worker': False,
            'stopped': (target / 'STOP.json').exists(), 'candidates_reserved': len(list((target / 'candidates').glob('c*'))),
            'budget': session['budget'], 'comparisons': summaries,
            'note': 'No automatic adoption; only three successful runs yield confirmed aggregate comparisons.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('initialize', 'register', 'run', 'summarize'))
    parser.add_argument('--problem', type=int, required=True, choices=(8, 11))
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--start', type=Path)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--hypothesis', type=Path)
    parser.add_argument('--name')
    parser.add_argument('--repetition', type=int, default=1)
    args = parser.parse_args()
    if os.environ.get('CLAUDE_JOB_DIR'):
        tempfile.tempdir = str(Path(os.environ['CLAUDE_JOB_DIR']) / 'tmp')
    with lock():
        if args.action == 'initialize':
            if args.repo is None or args.start is None:
                parser.error('initialize requires --repo and --start')
            initialize(args.problem, args.repo, args.start)
            result = {'initialized': args.problem}
        elif args.action == 'register':
            if args.candidate is None or args.hypothesis is None:
                parser.error('register requires --candidate and --hypothesis')
            result = {'registered': register(args.problem, args.candidate, args.hypothesis)}
        elif args.action == 'run':
            if args.name is None:
                parser.error('run requires --name')
            result = run(args.problem, args.name, args.repetition)
        else:
            result = summarize(args.problem)
            write(folder(args.problem) / ('summary-' + base.stamp().replace(':', '-') + '.json'), result)
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result.get('status', 'passed') == 'passed' else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, OSError, KeyError) as exc:
        sys.exit(str(exc))
