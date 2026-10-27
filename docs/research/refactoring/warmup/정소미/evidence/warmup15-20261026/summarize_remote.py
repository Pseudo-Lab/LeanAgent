"""Summarize downloaded frozen-checker artifacts; no APIs or Lean execution.

All inputs are local paths. Scores use controls from the same remote run.
Native screening is deliberately excluded. An artifact is evidence only when its
saved source/log hashes, three measurements and unchanged context all agree.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import statistics

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PRIMARY = {p: ('v4.31.0' if p <= 12 else 'v4.26.0') for p in range(10, 16)}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(path.read_text())


def checked(path, expected, errors):
    if not path.is_file():
        errors.append(f'Missing artifact: {path}')
        return ''
    data = path.read_bytes()
    if not expected or digest(data) != expected:
        errors.append(f'SHA mismatch: {path}')
    return data.decode('utf-8')


def context(text, proof, errors, normalize_nonce=False, trim_proof=True):
    # The Somi writer strips final newlines; frozen PR3 inserts exact input bytes.
    body = proof.rstrip('\n') if trim_proof else proof
    if not body or text.count(body) != 1:
        errors.append('Exact proof is not present exactly once in generated source')
        return None
    prefix, suffix = text.split(body)
    if normalize_nonce:
        prefix = re.sub(r'(?m)^(#refactor_eval )"[0-9a-f]+"', r'\1"<nonce>"', prefix)
    return {'prefixSha256': digest(prefix.encode()), 'suffixSha256': digest(suffix.encode())}


def common_candidate(item, proof, folder, target):
    errors, contexts, values = [], {}, []
    result = item['result']
    environments = result.get('environments', {})
    if len(environments) != 1:
        errors.append('Expected one pinned environment per remote artifact')
    for version_id, env in environments.items():
        for run in env.get('runs', []):
            source = checked(folder / version_id / run['source'], run.get('source_sha256'), errors)
            log = checked(folder / version_id / run['log'], run.get('log_sha256'), errors)
            kind = 'measure' if 'measurement' in run else 'check'
            ctx = context(source, proof, errors, normalize_nonce=kind == 'measure', trim_proof=False)
            if kind in contexts and contexts[kind] != ctx:
                errors.append('Context differs between repetitions')
            contexts[kind] = ctx
            if 'measurement' in run:
                measured = run['measurement']
                matches = re.findall(r'REFACTOR_EVAL [0-9a-f]+ (\{[^\n]*\})', log)
                if len(matches) != 1 or json.loads(matches[0]) != measured:
                    errors.append('Saved measurement differs from its log')
                if (measured.get('target') != target or not set(measured.get('axioms', [])) <= ALLOWED
                        or any(type(measured.get(k)) is not int or measured[k] < 0 for k in ('raw', 'scaled'))
                        or measured.get('scaled') != measured.get('raw', -1) // 1000):
                    errors.append('Invalid target, axioms or heartbeat unit')
                values.append(measured.get('scaled'))
        if env.get('valid') and (len(env.get('runs', [])) != 4 or len(values) != 3
                or any(r.get('returncode') != 0 or r.get('timed_out') for r in env['runs'])
                or env.get('median_heartbeats') != statistics.median(values)):
            errors.append('Claimed validity does not match three successful measurements')
    valid = bool(result.get('valid')) and all(e.get('valid') for e in environments.values()) and len(values) == 3 and not errors
    return {'reportedValid': bool(result.get('valid')), 'threeRunsValid': valid,
            'tokens': result.get('tokens'), 'heartbeats': statistics.median(values) if valid else None,
            'heartbeatRuns': values, 'contextHashes': contexts, 'artifactErrors': errors,
            'verificationError': next((e.get('error') for e in environments.values() if e.get('error')), None) or result.get('error')}


def p12_candidate(item, proof, folder, target):
    errors, contexts, values = [], {}, []
    for run in item.get('runs', []):
        for kind in ('check', 'hb'):
            source = checked(folder / f'{run["tag"]}.{kind}.lean', run.get(f'{kind}SourceSha256'), errors)
            checked(folder / f'{run["tag"]}.{kind}.log', run.get(f'{kind}LogSha256'), errors)
            ctx = context(source, proof, errors)
            if ctx != run.get('contextHashes', {}).get(kind):
                errors.append('Generated context differs from recorded context hash')
            if kind in contexts and contexts[kind] != ctx:
                errors.append('Context differs between repetitions')
            contexts[kind] = ctx
        hb = run.get('heartbeat', {})
        if run.get('valid') and (not run.get('statement_unchanged') or run.get('forbidden_patterns')
                or not run.get('compiled') or not run.get('allowedAxiomsOnly')
                or not set(run.get('actualAxioms', [])) <= ALLOWED
                or run.get('driverReturncode') != 0 or run.get('name') != target
                or run.get('candidate_sha256') != digest(proof.encode())
                or hb.get('returncode') != 0 or hb.get('timed_out') or hb.get('measurement_ambiguous')
                or type(hb.get('heartbeats')) is not int or hb.get('heartbeats', -1) < 0):
            errors.append('Claimed P12 validity differs from the full-source audit')
        if run.get('valid'):
            values.append(hb.get('heartbeats'))
    valid = bool(item.get('valid')) and len(values) == len(item.get('runs', [])) == 3 and not errors
    if valid and item.get('medianHeartbeats') != statistics.median(values):
        errors.append('P12 median differs from measured runs'); valid = False
    return {'reportedValid': bool(item.get('valid')), 'threeRunsValid': valid,
            'tokens': item.get('tokens'), 'heartbeats': statistics.median(values) if valid else None,
            'heartbeatRuns': values, 'contextHashes': contexts, 'artifactErrors': errors,
            'verificationError': next(({'kind': r.get('failureKind'), 'errors': r.get('check', {}).get('first_errors', [])}
                for r in item.get('runs', []) if not r.get('valid')), None)}


def load_proofs(snapshot, candidates):
    proofs = {digest(c['proof'].encode()): c['proof'] for p in snapshot['problems'] for c in p['teamResults']}
    for path in candidates:
        data = read(path)
        if isinstance(data.get('problems'), dict):
            entries = [c for cs in data['problems'].values() for c in cs]
        else:
            entries = data['candidates']
        for entry in entries:
            code = entry.get('proof')
            if code is None:
                candidate_path = Path(entry['path'])
                code = (candidate_path if candidate_path.is_absolute() else path.parent / candidate_path).read_text()
            expected = entry.get('candidateHash', entry.get('sha256'))
            if digest(code.encode()) != expected:
                raise ValueError(f'Candidate hash mismatch in {path}')
            proofs[expected] = code
    return proofs


def summarize(summary_path, data, metas, starts, proofs):
    output = []
    separate = data.get('source') == 'p12-separate'
    problems = [{'id': 12, 'candidates': data.get('candidates', {})}] if separate else data.get('problems', [])
    for problem in problems:
        ident = problem['id']
        if ident not in PRIMARY:
            continue
        meta, start = metas[ident], starts[ident]
        original_sha, starting_sha = digest(meta['src'].encode()), start['candidateHash']
        base = {'problem': ident, 'version': data['version'], 'primary': data['version'] == PRIMARY[ident],
                'runId': data.get('runId'), 'commit': data.get('commit'), 'revision': data.get('revision'),
                'startedAt': data.get('startedAt'), 'rawSummary': str(summary_path),
                'rawSummarySha256': digest(summary_path.read_bytes()), 'remoteStatus': data.get('status'),
                'originalSha256': original_sha, 'startingSha256': starting_sha,
                'protocol': data.get('protocol', 'frozen PR3'), 'countsInCommonScore': not separate}
        entries = dict(problem['candidates'])
        if not separate:
            entries = {'original': {'sha256': original_sha, 'result': problem['baseline']}, **entries}
        records = []
        for label, item in entries.items():
            sha = item['sha256']
            proof = meta['src'] if sha == original_sha else proofs.get(sha)
            folder = summary_path.parent / label if separate else summary_path.parent / f'P{ident:02d}' / ('baseline' if label == 'original' else sha[:16])
            if proof is None and separate and (summary_path.parent / f'{label}.lean').is_file():
                proof = (summary_path.parent / f'{label}.lean').read_text()
            if proof is None or digest(proof.encode()) != sha:
                measured = {'reportedValid': item.get('valid', item.get('result', {}).get('valid')),
                            'threeRunsValid': False, 'artifactErrors': ['Exact candidate source is unavailable or hash differs'],
                            'contextHashes': {}, 'tokens': None, 'heartbeats': None}
            else:
                audit = p12_candidate if separate else common_candidate
                measured = audit(item, proof, folder, meta['name'])
            role = 'original' if sha == original_sha else 'starting' if sha == starting_sha else 'candidate'
            records.append({**base, 'id': label, 'sha256': sha, 'role': role, 'rawFolder': str(folder), **measured})
        original = next((r for r in records if r['role'] == 'original'), None)
        starting = next((r for r in records if r['role'] == 'starting'), None)
        for row in records:
            row['sameContextAsOriginal'] = bool(original and row['contextHashes'] == original['contextHashes']
                and all(row['contextHashes'].get(k) for k in ('check', 'hb' if separate else 'measure')))
            row['valid'] = row['threeRunsValid'] and row['sameContextAsOriginal']
        controls = bool(original and starting and original['valid'] and starting['valid'])
        def score(row):
            return 50 * (2 - row['tokens'] / original['tokens'] - row['heartbeats'] / original['heartbeats'])
        for row in records:
            row['controlsValid'] = controls
            row['score'] = score(row) if controls and row['valid'] and original['tokens'] > 0 and original['heartbeats'] > 0 else None
            row['scoreDeltaVersusStarting'] = row['score'] - score(starting) if row['score'] is not None else None
        output.extend(records)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, action='append', required=True, help='Downloaded artifact directory or summary.json; repeatable')
    parser.add_argument('--benchmark', type=Path, required=True)
    parser.add_argument('--starting', type=Path, required=True)
    parser.add_argument('--candidates', type=Path, action='append', default=[], help='Candidate manifest or frozen experiment input; repeatable')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    metas = {i + 1: row for i, row in enumerate(json.loads(l) for l in args.benchmark.read_text().splitlines() if l.strip())}
    snapshot = read(args.starting); starts = {p['id']: p for p in snapshot['problems']}
    proofs = load_proofs(snapshot, args.candidates)
    paths = sorted({p.resolve() for path in args.input for p in ([path] if path.is_file() else path.rglob('summary.json'))})
    attempts, errors = [], []
    for path in paths:
        data = read(path)
        if data.get('source') not in {'arklib', 'putnambench', 'p12-separate'}:
            continue
        try:
            attempts.extend(summarize(path, data, metas, starts, proofs))
        except (KeyError, ValueError, OSError, TypeError) as error:
            errors.append({'rawSummary': str(path), 'error': str(error)})
    groups = []
    for key in sorted({(a['problem'], a['sha256']) for a in attempts}):
        matching = [a for a in attempts if (a['problem'], a['sha256']) == key]
        versions = [v for pin in metas[key[0]]['version_info'] for v in pin]
        compatibility = []
        for version in versions:
            found = [a for a in matching if a['version'] == version]
            passed = any(a['valid'] and a['controlsValid'] for a in found)
            if passed:
                status = 'pass'
            elif not found:
                status = 'pending'
            elif any(a['artifactErrors'] for a in found):
                status = 'evidence_invalid'
            elif not any(a['controlsValid'] for a in found):
                status = 'environment_or_control_failed'
            else:
                status = 'proof_failed'
            compatibility.append({'version': version, 'status': status,
                                  'evidence': [a['rawSummary'] for a in found]})
        groups.append({'problem': key[0], 'sha256': key[1], 'ids': sorted({a['id'] for a in matching}),
                       'role': matching[0]['role'], 'requiredVersions': versions,
                       'compatibilityComplete': all(x['status'] == 'pass' for x in compatibility),
                       'compatibility': compatibility,
                       'primaryEvidence': [{k: a[k] for k in ('rawSummary', 'runId', 'valid', 'controlsValid', 'tokens', 'heartbeats', 'score', 'scoreDeltaVersusStarting')}
                                           for a in matching if a['primary']]})
    result = {'schemaVersion': 1, 'nativeScreeningIncluded': False,
              'startingSha256': digest(args.starting.read_bytes()), 'benchmarkSha256': digest(args.benchmark.read_bytes()),
              'summaryReadErrors': errors, 'attempts': attempts, 'candidates': groups,
              'note': 'Use only valid three-run primary records with controlsValid. P12 uses a separate protocol. Compatibility requires the same SHA in every designated version; missing/environment/invalid evidence is not a zero score.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'attempts': len(attempts), 'artifactFailures': sum(bool(a['artifactErrors']) for a in attempts), 'summaryReadErrors': len(errors), 'output': str(args.output)}, ensure_ascii=False))


if __name__ == '__main__':
    main()
