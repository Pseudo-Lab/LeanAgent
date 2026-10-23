"""Pinned-context Lean verification and local measurements; never calls an LLM.

Run one environment at a time: python run_sweep.py SOURCE VERSION PROJECT_DIR [ID ...]
Results remain append-only per candidate/version. Artifact files are not submissions.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
from proof_tokens import proof_length

MEASURE = '''
elab "#arena_count " cmd:command : command => do
  let start ← IO.getNumHeartbeats
  Lean.Elab.Command.elabCommand (← `(command| set_option Elab.async false in $cmd))
  let finish ← IO.getNumHeartbeats
  Lean.logInfo m!"ARENA_HEARTBEATS_RAW={finish - start}"

'''


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def invoke(project, text, dest, output_olean=False, search_dir=None):
    dest.parent.mkdir(parents=True, exist_ok=True)
    path = dest.with_suffix('.lean')
    path.write_text(text)
    env = dict(os.environ)
    # Reuse the user's existing 4.26 installation; other toolchains are isolated.
    if os.environ.get('MIN_ELAN_HOME'):
        env['ELAN_HOME'] = os.environ['MIN_ELAN_HOME']
    if search_dir:
        env['LEAN_PATH']=str(search_dir)+os.pathsep+env.get('LEAN_PATH','')
    cmd = [str(Path.home()/'.elan/bin/lake'), 'env', 'lean', '--json']
    if output_olean:
        cmd += ['-R',str(dest.parent),'-o',str(dest.with_suffix('.olean'))]
    cmd += [str(path)]
    t = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=project, env=env, capture_output=True, text=True, timeout=180)
        rc, out, err = p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired as e:
        rc = None
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else e.stdout or ''
        err = 'TIMEOUT: 180s operational limit (not an Arena limit)'
    dest.with_suffix('.raw.jsonl').write_text(out)
    normalized=[]
    for line in out.splitlines():
        try:
            msg=json.loads(line)
            if isinstance(msg,dict) and 'data' in msg:
                pos=msg.get('pos') or {}
                normalized.append(f"{path}:{pos.get('line',0)}:{pos.get('column',0)}: {msg.get('severity','info')}: {msg['data']}")
            else: normalized.append(line)
        except json.JSONDecodeError: normalized.append(line)
    out='\n'.join(normalized)+'\n'
    dest.with_suffix('.stdout.txt').write_text(out)
    dest.with_suffix('.stderr.txt').write_text(err)
    obs = {'command': cmd, 'cwd': str(project), 'returncode': rc,
           'wall_seconds': time.monotonic()-t, 'stdout_path': str(dest.with_suffix('.stdout.txt')),
           'stderr_path': str(dest.with_suffix('.stderr.txt'))}
    save(dest.with_suffix('.run.json'), obs)
    return rc, out, err


def inspect_output(rc, out, err, name):
    pattern = re.escape(name) + r"'? depends on axioms: \[([^\]]*)\]"
    matches = re.findall(pattern, out, re.S)
    axioms = [a.strip() for a in matches[-1].replace('\n', '').split(',') if a.strip()] if matches else None
    if f"'{name}' does not depend on any axioms" in out:
        axioms = []
    if rc is None:
        kind = 'timeout'
    elif rc != 0:
        kind = 'environment_error' if any(s in out+err for s in ['object file', 'unknown module prefix', 'failed to download', 'no such file']) else 'invalid'
    elif axioms is None:
        kind = 'axiom_check_missing'
    elif set(axioms) - {'propext', 'Quot.sound', 'Classical.choice'}:
        kind = 'invalid_axioms'
    else:
        kind = 'valid'
    return {'kind': kind, 'axioms': axioms}


def context(row, project, version):
    if row['source'] == 'putnambench':
        source = row['header'] + '\n' + row['src'] + '\n'
    else:
        commit = next(pair[version] for pair in row['version_info'] if version in pair)
        source = subprocess.check_output(['git', 'show', commit+':'+row['file_path']], cwd=project, text=True)
    if source.count(row['src']) != 1 and row['name'].endswith('fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius'):
        # Inspected old commits differ by exactly this extra body-space. No
        # whitespace fuzzing of statements, strings, comments or arbitrary proofs.
        old=row['src'].replace('have h_elemenet_Y_bad : y_of_x', 'have h_elemenet_Y_bad :  y_of_x')
        if source.count(old)==1:
            source=source.replace(old,row['src'],1)
    if source.count(row['src']) != 1:
        # No fuzzy theorem matching or guessing body ranges across revisions.
        raise ValueError('Exact benchmark declaration not uniquely present in pinned source')
    decl_start = source.index(row['src'])
    tail = row['src'][len(row['statement']):]
    assert tail.lstrip().startswith(':=')
    body = tail.lstrip()[2:].lstrip()
    body_start = decl_start + len(row['src']) - len(body)
    body_end = decl_start + len(row['src'])
    assert source[body_start:body_end] == body
    return source, body_start, body_end, decl_start, body


def check(row, project, version, body, dest, ctx, measure=True):
    source, a, b, ds, original = ctx
    file = source[:a] + body + source[b:]
    # These authored candidates contain no commands in their bodies. Reject obvious
    # command injection; this is not a replacement for a general Lean AST firewall.
    forbidden = re.search(r'\b(sorry|admit|sorryAx|native_decide|unsafe|axiom)\b|^\s*(?:import|theorem|lemma|def|elab|macro|initialize|set_option)\b', body, re.M)
    if forbidden:
        return {'kind': 'contract_reject', 'reason': forbidden.group()}
    is_module=bool(re.search(r'^module\s*$',file,re.M))
    if is_module:
        rc,out,err=invoke(project,file,dest,output_olean=True)
        if rc==0:
            probe=f'import {dest.name}\n#print axioms {row["name"]}\n'
            prc,pout,perr=invoke(project,probe,Path(str(dest)+'_axioms'),search_dir=dest.parent)
            out+='\n'+pout;err+='\n'+perr
            if prc: rc=prc
        combined=dest.with_suffix('.combined.txt');combined.write_text(out)
    else:
        rc, out, err = invoke(project, file + '\n#print axioms ' + row['name']+'\n', dest)
    res = inspect_output(rc, out, err, row['name'])
    res.update(body_hash=sha(body), tokens=proof_length(row['statement']+' := '+body,row['statement']), output_path=str(dest.with_suffix('.combined.txt' if is_module else '.stdout.txt')))
    if res['kind'] == 'valid' and measure:
        # Add instrumentation only to a separate copy. Measure the declaration,
        # synchronously, with the original resource options retained.
        # The whole uninstrumented file was already verified above. Stop this
        # separate measurement copy immediately after the target declaration:
        # the custom command can affect section-variable tracking for later
        # `omit ... in` commands, which are outside the measured declaration.
        measured = source[:ds] + MEASURE + '#arena_count\n' + file[ds:a+len(body)] + '\n#exit\n'
        lines = measured.splitlines(True)
        module_lines=[i for i,l in enumerate(lines) if l.strip()=='module']
        k = module_lines[0]+1 if module_lines else 0
        lines.insert(k, 'import Lean\n')
        mrc, mout, merr = invoke(project, ''.join(lines), Path(str(dest)+'_measure'))
        counts = re.findall(r'ARENA_HEARTBEATS_RAW=(\d+)', mout)
        res['heartbeats_raw'] = int(counts[-1]) if mrc == 0 and counts else None
        res['heartbeats'] = res['heartbeats_raw']/1000 if res['heartbeats_raw'] is not None else None
        res['measurement_kind'] = 'local_o200k_base_and_synchronous_declaration_heartbeats'
    return res

