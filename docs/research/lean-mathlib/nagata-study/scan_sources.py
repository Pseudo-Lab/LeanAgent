#!/usr/bin/env python3
"""Reproduce a source-level Nagata inventory; never a Lean proof validator."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


def code_only(source):
    """Mask nested Lean block comments, line comments and strings; keep newlines."""
    output = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                output[i:i+2] = '  '; depth += 1; i += 2; continue
            if source.startswith('-/', i):
                output[i:i+2] = '  '; depth -= 1; i += 2; continue
            if source[i] != '\n': output[i] = ' '
            i += 1; continue
        if string:
            if source[i] == '\\' and i + 1 < len(source):
                output[i:i+2] = '  '; i += 2; continue
            if source[i] == '"': string = False
            if source[i] != '\n': output[i] = ' '
            i += 1; continue
        if source.startswith('/-', i):
            output[i:i+2] = '  '; depth = 1; i += 2; continue
        if source.startswith('--', i):
            end = source.find('\n', i)
            if end < 0: end = len(source)
            output[i:end] = ' ' * (end-i); i = end; continue
        if source[i] == '"':
            string = True; output[i] = ' '
        i += 1
    return ''.join(output)


def inventory(repo):
    lean = repo / 'lean'
    paths = sorted((lean / 'OAI/AlgebraicGeometry/PlaneCurves').glob('*.lean'))
    if not paths:
        raise SystemExit('PlaneCurves sources missing; populate the selected checkout first.')
    modules = {'.'.join(p.relative_to(lean).with_suffix('').parts): p for p in paths}
    imports, findings, hashes = {}, [], {}
    pattern = re.compile(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|run_tac)\b')
    for module, path in modules.items():
        source = path.read_text()
        stripped = code_only(source)
        imports[module] = re.findall(r'^import\s+(\S+)', stripped, re.M)
        hashes[str(path.relative_to(repo))] = hashlib.sha256(path.read_bytes()).hexdigest()
        for match in pattern.finditer(stripped):
            findings.append({'file':str(path.relative_to(repo)),
                             'line':stripped.count('\n', 0, match.start())+1,
                             'token':match.group()})
    seen, frontier = set(), set()
    pending = ['OAI.AlgebraicGeometry.PlaneCurves.Nagata']
    while pending:
        mod = pending.pop()
        if mod in seen: continue
        if mod not in modules: frontier.add(mod); continue
        seen.add(mod); pending.extend(imports[mod])
    config = json.loads((lean/'ComparatorChallenges/Nagata.json').read_text())
    return {
        'review_date':'2026-10-07',
        'repository':'https://github.com/openai/math',
        'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),
        'lean_toolchain':(lean/'lean-toolchain').read_text().strip(),
        'mathlib_revision':next(p['rev'] for p in json.loads((lean/'lake-manifest.json').read_text())['packages'] if p['name']=='mathlib'),
        'scope':f'{len(paths)}-file PlaneCurves source subtree and selected Comparator/paper files; Mathlib not scanned',
        'plane_curve_files':len(paths),
        'source_lines':sum(len(p.read_text().splitlines()) for p in paths),
        'reachable_present_modules':len(seen),
        'external_import_frontier':sorted(frontier),
        'source_keyword_findings':findings,
        'keyword_scan_limit':'Lexical scan, not Lean parsing or transitive proof-term axiom analysis.',
        'comparator_config':config,
        'runtime_checks':{'lake_build':'not_run','print_axioms':'not_run','comparator':'not_run','nanoda':'not_run'},
        'runtime_reason':'Pinned Lean v4.34.1 and matching dependencies absent; comparator/landrun/lean4export absent. No replacement toolchain used.',
        'module_imports':imports,
        'source_sha256':hashes,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = inventory(args.repository.resolve())
    args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(f"{result['plane_curve_files']} files, {result['source_lines']} lines, "
          f"{len(result['source_keyword_findings'])} implementation keyword findings; source review only.")
