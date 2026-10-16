#!/usr/bin/env python3
"""Build the corpus report from saved statistics or explicitly supplied exports.

Use --render-only for the checked-in analysis.json, or --results-root PATH for
full descriptive reanalysis of the restored corpus/results exports.
Python standard library only; does not run Lean or call a model.
"""
from __future__ import annotations

from collections import Counter
import argparse
import csv
import gzip
import hashlib
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parents[1]
SOURCES = ('strata', 'physlib', 'cslib', 'arklib', 'putnambench', 'leanpool')
LABELS = dict(zip(SOURCES, ('Strata', 'PhysLib', 'CSLib', 'ArkLib', 'PutnamBench', 'LeanPool')))
TACTICS = ('simp', 'rw', 'simp_all', 'grind', 'exact', 'apply', 'intro', 'intros',
           'induction', 'cases', 'ext', 'ring', 'norm_num', 'omega', 'fun_prop', 'aesop')


def load(path):
    return json.loads(path.read_text())


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def rows(path):
    with gzip.open(path, 'rt', encoding='utf-8') as stream:
        for line in stream:
            if line.strip():
                yield json.loads(line)


def percentile(hist, q):
    n = sum(hist.values())
    if not n:
        return None
    pos = (n - 1) * q
    lo, hi = math.floor(pos), math.ceil(pos)
    a = b = None
    seen = 0
    for value, count in sorted(hist.items()):
        if seen <= lo < seen + count:
            a = value
        if seen <= hi < seen + count:
            b = value
            break
        seen += count
    return round(a + (b - a) * (pos - lo), 4)


def stats(hist):
    n = sum(hist.values())
    return {'n': n, 'mean': round(sum(v * c for v, c in hist.items()) / n, 4) if n else None,
            'median': percentile(hist, .5), 'p90': percentile(hist, .9),
            'p95': percentile(hist, .95), 'p99': percentile(hist, .99),
            'min': min(hist) if n else None, 'max': max(hist) if n else None}


def percent(a, b):
    return round(100 * a / b, 6) if b else None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--render-only', action='store_true', help='Rebuild HTML/CSV from the checked-in statistics; no raw-data reanalysis')
    mode.add_argument('--results-root', type=Path, help='Restored corpus/results directory for full descriptive reanalysis')
    args = parser.parse_args()
    if args.render_only:
        output = load(HERE / 'analysis.json')
        write_outputs(output, write_analysis=False)
        print(json.dumps({'status': 'passed', 'mode': 'render_only', 'statistics_recomputed': False,
                          'totals': output['totals']}, ensure_ascii=False, indent=2))
        return
    results_root = args.results_root.resolve()
    paths = {key: results_root / name for key, name in {
        'all_sources': 'all_sources/summary.json', 'lengths': 'proof_lengths/summary.json',
        'candidates': 'warmup_candidates/summary.json', 'length_records': 'proof_lengths/lengths.jsonl.gz',
        'tactic_records': 'all_sources/declarations.jsonl.gz'}.items()}
    if any(not p.exists() for p in paths.values()):
        raise SystemExit('Missing exported inputs. See the evidence README, then pass the restored corpus/results directory with --results-root.')
    base, old_lengths, selected = (load(paths[k]) for k in ('all_sources', 'lengths', 'candidates'))
    # Detect a different or altered export before recomputing the report.
    old_tactic_check = load(results_root / 'all_sources/verification.json')
    old_length_check = load(results_root / 'proof_lengths/validation.json')
    assert sha(paths['all_sources']) == old_tactic_check['summary_sha256']
    assert sha(paths['tactic_records']) == old_tactic_check['declarations_sha256']
    assert sha(paths['lengths']) == old_length_check['summary_sha256']
    hist = {s: {name: Counter() for name in old_lengths['sources'][s]['subsets']} for s in SOURCES}
    primary = {s: set() for s in SOURCES}
    fingerprints = {s: Counter() for s in SOURCES}
    fingerprint_lengths = {s: {} for s in SOURCES}
    length_records = Counter()
    for row in rows(paths['length_records']):
        s, length = row['source'], row['proof_length']
        length_records[s] += 1
        assert row['proof_style'] in ('by', 'term')
        hist[s]['assignment_all'][length] += 1
        if row['proof_style'] == 'by':
            hist[s]['by_all'][length] += 1
        if not row['contains_sorry']:
            hist[s]['assignment_no_direct_sorry'][length] += 1
            subset = 'by_no_direct_sorry' if row['proof_style'] == 'by' else 'term_no_direct_sorry'
            hist[s][subset][length] += 1
            if row['proof_style'] == 'by':
                assert row['id'] not in primary[s]
                primary[s].add(row['id'])
                digest = bytes.fromhex(row['proof_sha256'])
                fingerprints[s][digest] += 1
                if digest in fingerprint_lengths[s]:
                    assert fingerprint_lengths[s][digest] == length
                fingerprint_lengths[s][digest] = length
    checks = 0
    for s in SOURCES:
        for name, counter in hist[s].items():
            expected = old_lengths['sources'][s]['subsets'][name]
            assert dict(counter) == {int(k): v for k, v in expected['histogram'].items()}, (s, name)
            new = stats(counter)
            for old_key, new_key in [('n', 'n'), ('p50', 'median'), ('mean', 'mean'), ('p90', 'p90'), ('p99', 'p99')]:
                assert expected[old_key] == new[new_key], (s, name, old_key)
            checks += 1
    files = {s: Counter() for s in SOURCES}
    uses = {s: Counter() for s in SOURCES}
    occurrences = {s: Counter() for s in SOURCES}
    exported_all = Counter()
    exported_no_sorry = Counter()
    exported_no_sorry_uses = {s: Counter() for s in SOURCES}
    tactic_seen = {s: set() for s in SOURCES}
    for row in rows(paths['tactic_records']):
        s = row['source']
        if s not in SOURCES:  # Arena's three completed Putnam references stay separate.
            assert s == 'putnambench_warmup'
            continue
        exported_all[s] += 1
        heads = row['heads']
        if not row['contains_sorry']:
            exported_no_sorry[s] += 1
            exported_no_sorry_uses[s].update(heads.keys())
        if row['id'] in primary[s]:
            assert row['id'] not in tactic_seen[s]
            tactic_seen[s].add(row['id'])
            files[s][row['file_path']] += 1
            uses[s].update(heads.keys())
            occurrences[s].update(heads)
    sources = []
    total_declarations = sum(base['sources'][s]['subsets']['all']['declarations'] for s in SOURCES)
    for s in SOURCES:
        old = base['sources'][s]
        all_count = old['subsets']['all']['declarations']
        no_sorry = old['subsets']['no_direct_sorry']['declarations']
        assert exported_all[s] == all_count
        assert exported_no_sorry[s] == no_sorry
        assert tactic_seen[s] == primary[s]
        assert sum(files[s].values()) == len(primary[s])
        for item in old['subsets']['no_direct_sorry']['heads']:
            assert item['declarations'] == exported_no_sorry_uses[s][item['name']]
        h = hist[s]['by_no_direct_sorry']
        n = sum(h.values())
        candidates = {k: v for k, v in selected['sources'][s].items() if k != 'exports'}
        ge200 = sum(c for length, c in h.items() if length >= 200)
        cutoff = candidates['top5pct_cutoff']
        top = sum(c for length, c in h.items() if cutoff is not None and length >= cutoff)
        assert candidates['eligible'] == n and candidates['ge200'] == ge200
        assert candidates['top5pct'] == top
        assert candidates['intersection'] == sum(c for length, c in h.items() if cutoff is not None and length >= max(200, cutoff))
        unique_hist = Counter(fingerprint_lengths[s].values())
        unique_ge200 = sum(length >= 200 for length in fingerprint_lengths[s].values())
        total_tokens = sum(length * count for length, count in h.items())
        top_tokens = sum(length * count for length, count in h.items() if cutoff is not None and length >= cutoff)
        head_map = {item['name']: item for item in old['subsets']['no_direct_sorry']['heads']}
        manifest = old['manifest']
        sources.append({
            'id': s, 'label': LABELS[s], 'files_scanned': manifest['files_scanned'],
            'declarations': all_count, 'share_percent': percent(all_count, total_declarations),
            'no_direct_sorry': no_sorry, 'direct_sorry': all_count - no_sorry,
            'eligible': n, 'other_no_direct_sorry': no_sorry - n,
            'revision': manifest['revision'], 'toolchain': manifest['toolchain'],
            'repository': manifest.get('url', manifest.get('source')),
            'extraction_methods': old['extraction_methods'],
            'length': stats(h), 'length_histogram': sorted(h.items()),
            'bins': old_lengths['sources'][s]['subsets']['by_no_direct_sorry']['bin_percent'],
            'bin_counts': old_lengths['sources'][s]['subsets']['by_no_direct_sorry']['bin_counts'],
            'candidates': candidates,
            'tail': {'top_with_ties_count': top, 'top_token_share_percent': percent(top_tokens, total_tokens),
                     'ge200_percent': percent(ge200, n)},
            'duplicates': {'method': 'Exact proof UTF-8 SHA-256, within source, by_no_direct_sorry only; whitespace retained',
                           'unique_proof_strings': sum(unique_hist.values()),
                           'redundant_records': n - sum(unique_hist.values()),
                           'redundant_percent': percent(n - sum(unique_hist.values()), n),
                           'ge200_unique': unique_ge200, 'ge200_redundant_percent': percent(ge200 - unique_ge200, ge200),
                           'unique_string_lengths': stats(unique_hist),
                           'largest_group': max(fingerprints[s].values(), default=0)},
            'file_concentration': {'files': len(files[s]),
                                   'top1_percent': percent(sum(v for _, v in files[s].most_common(1)), n),
                                   'top10_percent': percent(sum(v for _, v in files[s].most_common(10)), n),
                                   'top_files': [{'file': p, 'count': c} for p, c in files[s].most_common(5)]},
            'tactics': {name: {'uses': uses[s][name], 'occurrences': occurrences[s][name],
                               'percent': percent(uses[s][name], n),
                               'all_styles_uses': head_map.get(name, {}).get('declarations', 0),
                               'all_styles_percent': percent(head_map.get(name, {}).get('declarations', 0), no_sorry)} for name in TACTICS}
        })
    valid_sources = [s for s in sources if s['eligible']]
    pooled = sum(s['eligible'] for s in sources)
    balance = {t: {'pooled_percent': percent(sum(s['tactics'][t]['uses'] for s in sources), pooled),
                   'equal_source_mean_percent': round(sum(s['tactics'][t]['percent'] for s in valid_sources) / len(valid_sources), 6)} for t in TACTICS}
    output = {
        'schema_version': 1, 'analysis_date': '2026-10-16',
        'snapshot_commit': 'b740bc5172c4d292b0bad1199ac550a0c56a38e5',
        'scope': 'Static descriptive reanalysis; not Lean compilation, theorem validation, heartbeat profiling, or model generation.',
        'primary_population': 'proof_style=by AND contains_sorry=false; source-level lexical filter, not kernel validity',
        'methods': {'quantiles': 'Linear interpolation at rank (n-1)*q',
                    'duplicates': 'Within-source exact proof text SHA-256, including whitespace; not theorem or semantic identity',
                    'tail': 'All records at or above the ceil(N/20)-th longest length; boundary ties included',
                    'tactics': 'Presence per proof from existing approximate lexical exports; not runtime call counts',
                    'equal_source_mean': 'Unweighted arithmetic mean across the five sources with a nonempty primary population'},
        'input_sha256': {'corpus/results/' + str(p.relative_to(results_root)): sha(p) for p in paths.values()},
        'totals': {'files_scanned': sum(s['files_scanned'] for s in sources), 'declarations': total_declarations,
                   'no_direct_sorry': sum(s['no_direct_sorry'] for s in sources), 'eligible': pooled,
                   'length_records_checked': sum(length_records.values()), 'histograms_checked': checks,
                   'ge200': sum(s['candidates']['ge200'] for s in sources),
                   'intersection': sum(s['candidates']['intersection'] for s in sources)},
        'sources': sources, 'tactic_order': list(TACTICS), 'balance': balance,
        'length_bin_labels': old_lengths['bins']['labels'],
        'warmup': old_lengths['warmup_rows'], 'warmup_statistics': old_lengths['warmup'],
        'calibration': old_lengths['calibration'],
        'leanpool_groups': [{'group': k, 'count': v, 'percent': percent(v, base['sources']['leanpool']['subsets']['all']['declarations'])}
                            for k, v in list(base['sources']['leanpool']['leanpool_path_group_declarations'].items())[:10]],
        'validation': {'status': 'passed', 'exported_tactic_rows_checked': sum(exported_all.values()),
                       'all_length_histograms_recomputed': True, 'original_summaries_unchanged': True,
                       'lean_executed': False, 'heartbeat_measured': False}
    }
    write_outputs(output, write_analysis=True)
    print(json.dumps({'status': 'passed', 'mode': 'full_reanalysis', 'totals': output['totals']}, ensure_ascii=False, indent=2))


def write_outputs(output, write_analysis):
    sources = output['sources']
    if write_analysis:
        (HERE / 'analysis.json').write_text(json.dumps(output, ensure_ascii=False, indent=2) + '\n')
    columns = ['source', 'files_scanned', 'declarations', 'direct_sorry', 'primary_n', 'median', 'mean', 'p90', 'p99',
               'ge200', 'top5_cutoff', 'intersection', 'exact_unique_proofs', 'redundant_percent', 'ge200_redundant_percent', 'top10_files_percent']
    with (HERE / 'source-summary.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        for s in sources:
            writer.writerow(dict(zip(columns, [s['label'], s['files_scanned'], s['declarations'], s['direct_sorry'], s['eligible'],
                                               s['length']['median'], s['length']['mean'], s['length']['p90'], s['length']['p99'],
                                               s['candidates']['ge200'], s['candidates']['top5pct_cutoff'], s['candidates']['intersection'],
                                               s['duplicates']['unique_proof_strings'], s['duplicates']['redundant_percent'],
                                               s['duplicates']['ge200_redundant_percent'], s['file_concentration']['top10_percent']])))
    template = HERE / 'report-template.html'
    if template.exists():
        raw = template.read_text()
        assert raw.count('@@DATA@@') == 1
        embedded = json.dumps(output, ensure_ascii=False, separators=(',', ':')).replace('<', '\\u003c')
        (AUTHOR / 'report.html').write_text(raw.replace('@@DATA@@', embedded))


if __name__ == '__main__':
    main()
