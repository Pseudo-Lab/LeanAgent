#!/usr/bin/env python3
"""validation-mini harness: real Lean runs + fixed local repair list + offline policy rendering.

No external API is called. Lean is executed through `lake env lean` inside the
pinned project directories listed in PROJECTS. Every Lean file that is compiled is
kept under cases/<ID>/attempts or cases/<ID>/logs together with its command and
raw stdout/stderr.

Usage:
  python3 reproduce.py env                 # record environment pins -> manifest.json (env part)
  python3 reproduce.py case R01 [R02 ...]  # run cases (real Lean)
  python3 reproduce.py all                 # all R cases
  python3 reproduce.py policy              # re-render decision.json from saved request.json (no Lean)
  python3 reproduce.py fixtures            # check P01..P04 synthetic fixtures (no Lean)

Paths of the pinned projects can be overridden with STRATA_DIR / TOY_DIR / LAKE.
"""
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))  # escalation_policy.py lives one level up
import escalation_policy  # noqa: E402

HOME = Path.home()
LAKE = os.environ.get("LAKE", str(HOME / ".elan/bin/lake"))
PROJECTS = {
    "strata": {
        "dir": os.environ.get("STRATA_DIR", str(HOME / "lean_project/refactor_arena/strata")),
        "has_aesop": False,
        "has_count_heartbeats": False,
    },
    "mathlib_toy": {
        "dir": os.environ.get("TOY_DIR", str(HOME / "lean_project/autoformalization_lab")),
        "has_aesop": True,
        "has_count_heartbeats": True,
    },
}
TIMEOUT_S = 300
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}

# Frozen BEFORE any case was run (v1). Not tuned per case. See manifest.json.
LOCAL_OPS_V1 = [
    {"op": "delete_span", "tactic": None},
    {"op": "replace_span", "tactic": "assumption"},
    {"op": "replace_span", "tactic": "rfl"},
    {"op": "replace_span", "tactic": "omega"},
    {"op": "replace_span", "tactic": "simp_all"},
    {"op": "replace_span_extract", "tactic": "simp?"},
    {"op": "replace_span_extract", "tactic": "exact?"},
    {"op": "replace_span_extract", "tactic": "aesop?", "requires": "aesop"},
]
LOCAL_POLICY_V1 = {
    "version": "local-ops-v1",
    "frozen_at": "2026-10-15T21:10+09:00 (before the first case run)",
    "target": "first error inside the target declaration of the candidate",
    "span": "error line plus following lines with strictly larger indentation (text heuristic, not a parser)",
    "unsolved_goals_rule": "if the first error message starts with 'unsolved goals', ops append the solver at the end of "
                           "the reported block instead of replacing/deleting it (delete_span is skipped)",
    "rounds": 1,
    "stop_rule": "stop at the first op whose whole-file replay is valid",
    "extract_rule": "for *? ops take the 'Try this' suggestion reported inside the span, substitute it and re-check",
    "timeout_s_per_lean_run": TIMEOUT_S,
    "ops": LOCAL_OPS_V1,
}


def sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def jdump(obj, path):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def jload(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


# ---------------------------------------------------------------- environment

def sh(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return p.stdout.strip() if p.returncode == 0 else f"ERROR({p.returncode}): {p.stderr.strip()[:300]}"


def environment_record():
    env = {}
    for name, p in PROJECTS.items():
        d = p["dir"]
        rec = {
            "dir": d,
            "lean_version": sh([LAKE, "env", "lean", "--version"], d),
            "lake_version": sh([LAKE, "--version"], d),
            "lean_toolchain": Path(d, "lean-toolchain").read_text().strip(),
            "repo_commit": sh(["git", "rev-parse", "HEAD"], d),
            "lake_manifest_sha256": file_sha(Path(d, "lake-manifest.json")),
            "lakefile_sha256": {f: file_sha(Path(d, f)) for f in ("lakefile.toml", "lakefile.lean") if Path(d, f).exists()},
            "uncommitted_status": sh(["git", "status", "--short", "--untracked-files=no"], d).splitlines(),
            "uncommitted_diff_sha256": sha(sh(["git", "diff"], d)),
            "packages": {pk["name"]: pk["rev"] for pk in jload(Path(d, "lake-manifest.json"))["packages"]},
            "has_aesop": p["has_aesop"],
        }
        rec["environment_hash"] = sha(json.dumps(
            {k: rec[k] for k in ("lean_version", "lean_toolchain", "repo_commit", "lake_manifest_sha256",
                                 "lakefile_sha256", "uncommitted_diff_sha256")}, sort_keys=True))
        env[name] = rec
    return env


_ENV = None


def env_for(project):
    global _ENV
    if _ENV is None:
        path = HERE / "environment.json"
        _ENV = jload(path) if path.exists() else environment_record()
        if not path.exists():
            jdump(_ENV, path)
    return _ENV[project]


# ---------------------------------------------------------------- Lean runner

DIAG_RE = re.compile(r"^(?P<path>.+?):(?P<line>\d+):(?P<col>\d+): (?P<sev>error|warning|info)(?:\([^)]*\))?: ?(?P<msg>.*)$")
SEV = {"error": "error", "warning": "warning", "information": "info", "info": "info"}


def parse_diagnostics(stdout, lean_path):
    """Parse `lean --json` output (one JSON message per line); unparsable lines are kept verbatim."""
    diags = []
    for raw in stdout.splitlines():
        if not raw.strip():
            continue
        try:
            j = json.loads(raw)
            pos = j.get("pos") or {}
            diags.append({"severity": SEV.get(j.get("severity"), j.get("severity")), "line": pos.get("line"),
                          "col": pos.get("column"), "message": (j.get("data") or "").rstrip(),
                          **({"end_line": j["endPos"]["line"], "end_col": j["endPos"]["column"]}
                             if j.get("endPos") else {})})
            continue
        except (json.JSONDecodeError, AttributeError):
            pass
        m = DIAG_RE.match(raw)
        if m:
            diags.append({"severity": m.group("sev"), "line": int(m.group("line")), "col": int(m.group("col")),
                          "message": m.group("msg")})
        else:
            diags.append({"severity": "unparsed", "line": None, "col": None, "message": raw})
    return diags


def run_lean(project, lean_text, out_stem):
    """Write lean_text to out_stem.lean, compile it, keep cmd/stdout/stderr/result."""
    out_stem = Path(out_stem)
    out_stem.parent.mkdir(parents=True, exist_ok=True)
    lean_path = out_stem.with_suffix(".lean")
    lean_path.write_text(lean_text, encoding="utf-8")
    cwd = PROJECTS[project]["dir"]
    cmd = [LAKE, "env", "lean", "--json", str(lean_path)]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=TIMEOUT_S)
        rc, out, err, timed_out = p.returncode, p.stdout, p.stderr, False
    except subprocess.TimeoutExpired as e:
        rc, out, err, timed_out = None, (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or ""), \
            (e.stderr or b"").decode() if isinstance(e.stderr, bytes) else (e.stderr or ""), True
    wall = round(time.time() - t0, 2)
    Path(str(out_stem) + ".cmd.txt").write_text(f"cd {cwd}\n{' '.join(cmd)}\n", encoding="utf-8")
    Path(str(out_stem) + ".stdout.txt").write_text(out, encoding="utf-8")
    Path(str(out_stem) + ".stderr.txt").write_text(err, encoding="utf-8")
    res = {"lean_file": rel(lean_path), "exit_code": rc, "timed_out": timed_out, "wall_s_local": wall,
           "diagnostics": parse_diagnostics(out, lean_path)}
    jdump(res, str(out_stem) + ".result.json")
    return res


def rel(p):
    try:
        return str(Path(p).resolve().relative_to(HERE))
    except ValueError:
        return str(p)


# ---------------------------------------------------------------- source / body handling

class Target:
    """Fixed original file, trusted body range (character offsets) and declaration metadata."""

    def __init__(self, spec):
        self.spec = spec
        self.project = spec["project"]
        self.source_path = HERE / spec["source"]
        self.source = self.source_path.read_text(encoding="utf-8")
        decl_src = spec["decl_src"]  # statement + " := " + original body, exactly once in the file
        assert self.source.count(decl_src) == 1, f"declaration text not unique in {spec['source']}"
        start = self.source.find(decl_src)
        stmt = spec["statement"]
        assert decl_src.startswith(stmt) and decl_src[len(stmt):len(stmt) + 4] == " := "
        self.decl_start = start
        self.body_start = start + len(stmt) + 4
        self.body_end = start + len(decl_src)
        self.original_body = self.source[self.body_start:self.body_end]
        self.decl_first_line = self.source[:start].count("\n") + 1
        self.body_first_line = self.source[:self.body_start].count("\n") + 1
        self.prefix = self.source[:self.body_start]
        self.suffix = self.source[self.body_end:]

    def file_with(self, body):
        return self.prefix + body + self.suffix

    def decl_last_line(self, body):
        return self.body_first_line + body.count("\n")

    def check_text(self, body):
        """Candidate file + appended axiom query (instrumentation outside the contract region)."""
        return self.file_with(body) + f"\n#print axioms {self.spec['full_name']}\n"

    def immutable_context_hash(self):
        return sha(self.prefix + "\x00<BODY>\x00" + self.suffix)


def classify(target, body, res):
    first, last = target.decl_first_line, target.decl_last_line(body)
    inside = [d for d in res["diagnostics"] if d["line"] is not None and first <= d["line"] <= last]
    errors_in = [d for d in inside if d["severity"] == "error"]
    sorry_in = [d for d in inside if d["severity"] == "warning" and "declaration uses 'sorry'" in d["message"]]
    axiom_line = target.file_with(body).count("\n") + 2
    axiom_msgs = [d for d in res["diagnostics"] if d["line"] == axiom_line]
    errors_out = [d for d in res["diagnostics"] if d["severity"] == "error" and d not in errors_in
                  and d not in axiom_msgs]
    axioms = None
    for d in axiom_msgs:
        m = re.search(r"depends on axioms: \[(.*?)\]", d["message"], re.S)
        if m:
            axioms = [a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()]
        elif "does not depend on any axioms" in d["message"]:
            axioms = []
    if res["timed_out"]:
        kind = "timeout"
    elif errors_in or sorry_in:
        kind = "invalid"
    elif errors_out:
        kind = "context_error"
    elif res["exit_code"] != 0:
        kind = "environment_error"
    elif axioms is None:
        kind = "axiom_check_missing"
    elif set(axioms) - STANDARD_AXIOMS:
        kind = "nonstandard_axioms"
    else:
        kind = "valid"
    return {"kind": kind, "errors_in_target": errors_in, "sorry_in_target": bool(sorry_in),
            "errors_outside_target": errors_out, "axioms": axioms,
            "first_error": errors_in[0] if errors_in else None}


def verify(target, body, stem):
    res = run_lean(target.project, target.check_text(body), stem)
    c = classify(target, body, res)
    c["run"] = rel(str(stem) + ".result.json")
    c["exit_code"] = res["exit_code"]
    c["wall_s_local"] = res["wall_s_local"]
    return c


# ---------------------------------------------------------------- body line helpers

def indent_of(line):
    return len(line) - len(line.lstrip(" "))


def span_of(lines, i):
    j = i + 1
    while j < len(lines) and (not lines[j].strip() or indent_of(lines[j]) > indent_of(lines[i])):
        j += 1
    while j - 1 > i and not lines[j - 1].strip():
        j -= 1
    return i, j  # [i, j)


BULLET_RE = re.compile(r"^(\s*)([·.]\s+)?(.*)$")


def body_line_of(target, diag):
    return diag["line"] - target.body_first_line  # 0 == the line holding `by`


def replace_span(lines, i, j, tactic):
    m = BULLET_RE.match(lines[i])
    ind, bullet = m.group(1), m.group(2) or ""
    t_lines = tactic.strip("\n").split("\n")
    out = [ind + bullet + t_lines[0]]
    cont = ind + " " * len(bullet)
    out += [cont + t for t in t_lines[1:]]
    return lines[:i] + out + lines[j:]


def append_after_span(lines, i, j, tactic):
    if i == 0:
        ind = " " * (indent_of(lines[1]) if len(lines) > 1 else 2)
    elif j - i > 1:
        ind = " " * indent_of(lines[i + 1])
    else:
        m = BULLET_RE.match(lines[i])
        ind = " " * (len(m.group(1)) + len(m.group(2) or "") or indent_of(lines[i]) + 2)
    t_lines = tactic.strip("\n").split("\n")
    return lines[:j] + [ind + t for t in t_lines] + lines[j:]


def suggestion_in(res, first_line, last_line):
    """Return the text of the first 'Try this' message reported within [first_line, last_line]."""
    for d in res["diagnostics"]:
        if d["line"] is None or not (first_line <= d["line"] <= last_line):
            continue
        msg = d["message"]
        if "Try this" not in msg:
            continue
        txt = msg.split("Try this:", 1)[1]
        txt = re.sub(r"^\s*\[apply\]\s*", "", txt.lstrip("\n"))
        tl = txt.split("\n")
        # dedent continuation lines
        rest = [l for l in tl[1:] if l.strip()]
        k = min((indent_of(l) for l in rest), default=0)
        tl = [tl[0].strip()] + [l[k:] for l in tl[1:]]
        while tl and not tl[-1].strip():
            tl.pop()
        text = "\n".join(tl)
        if re.search(r"\b(sorry|admit)\b", text):
            continue  # e.g. failed aesop? prints `Try this: sorry`; never substitute it
        return text, d
    return None, None


# ---------------------------------------------------------------- instrumented state capture

def capture_state(target, body, first_error, stem):
    """Insert `trace_state` before the failing tactic in a separate, instrumented run.

    The output is an OBSERVATION of an instrumented file, not a runner certificate:
    there is no clean-prefix replay digest, so it must never be passed as trusted state.
    """
    if first_error is None:
        return None, "no error"
    lines = body.split("\n")
    i = body_line_of(target, first_error)
    if i <= 0 or i >= len(lines):
        return None, "error not on a tactic line inside the body (reported at `by`/statement)"
    line = lines[i]
    s = line.strip()
    if s.startswith(("case ", "next ", "|", "<;>")) or (i > 0 and lines[i - 1].rstrip().endswith("<;>")):
        return None, "error line is a case/next/alternative/combinator line; trace_state insertion would change structure"
    m = BULLET_RE.match(line)
    ind, bullet, rest = m.group(1), m.group(2) or "", m.group(3)
    if bullet:
        new = [ind + bullet + "trace_state", ind + " " * len(bullet) + rest]
    else:
        new = [ind + "trace_state", line]
    inst = "\n".join(lines[:i] + new + lines[i + 1:])
    res = run_lean(target.project, target.file_with(inst), stem)
    abs_line = target.body_first_line + i
    traces = [d for d in res["diagnostics"] if d["line"] == abs_line and d["severity"] == "info"]
    if not traces:
        return None, f"trace_state produced no info message at line {abs_line}; see {rel(str(stem) + '.stdout.txt')}"
    return {"source": "instrumented_trace_state_run", "trusted": False,
            "untrusted_reason": "no clean-prefix replay certificate / state digest (Lean adapter not implemented)",
            "file_line": abs_line, "body_line": i, "goals_text": traces[0]["message"],
            "run": rel(str(stem) + ".result.json")}, None


# ---------------------------------------------------------------- local repair

def local_repair(target, body, first, attempts_dir):
    lines = body.split("\n")
    i = body_line_of(target, first)
    unsolved = first["message"].startswith("unsolved goals")
    if i < 0:
        i = 0
    i, j = span_of(lines, i) if i > 0 else (0, len(lines))
    span_first, span_last = target.body_first_line + i, target.body_first_line + j - 1
    attempts, success = [], None
    has_aesop = PROJECTS[target.project]["has_aesop"]
    for n, op in enumerate(LOCAL_OPS_V1, 1):
        name = f"{n:02d}_{op['op']}_{(op['tactic'] or 'none').replace('?', 'Q')}"
        rec = {"n": n, "op": op["op"], "tactic": op["tactic"], "span_body_lines": [i, j - 1],
               "span_text": "\n".join(lines[i:j])}
        if op.get("requires") == "aesop" and not has_aesop:
            rec.update(result="skipped", reason="Aesop not available in pinned environment (not added)")
            attempts.append(rec)
            continue
        if unsolved and op["op"] == "delete_span":
            rec.update(result="skipped", reason="unsolved-goals error: deleting the block cannot close goals")
            attempts.append(rec)
            continue
        tac = op["tactic"]
        if op["op"] == "delete_span":
            new_lines = lines[:i] + lines[j:]
        elif unsolved:
            new_lines = append_after_span(lines, i, j, tac)
        else:
            new_lines = replace_span(lines, i, j, tac)
        new_body = "\n".join(new_lines)
        stem = attempts_dir / name
        (attempts_dir / (name + ".body.txt")).parent.mkdir(parents=True, exist_ok=True)
        (attempts_dir / (name + ".body.txt")).write_text(new_body, encoding="utf-8")
        c = verify(target, new_body, stem)
        rec["check"] = summarize_check(c)
        if op["op"] == "replace_span_extract":
            res = jload(str(stem) + ".result.json")
            ins = target.body_first_line + (j if unsolved else i)
            sugg, d = suggestion_in(res, ins, ins)
            rec["raw_tool_output"] = d["message"] if d else None
            if sugg is None:
                rec.update(result="no_suggestion")
                attempts.append(rec)
                continue
            rec["suggestion"] = sugg
            ext_lines = append_after_span(lines, i, j, sugg) if unsolved else replace_span(lines, i, j, sugg)
            ext_body = "\n".join(ext_lines)
            (attempts_dir / (name + "_substituted.body.txt")).write_text(ext_body, encoding="utf-8")
            c = verify(target, ext_body, attempts_dir / (name + "_substituted"))
            rec["substituted_check"] = summarize_check(c)
            new_body = ext_body
        rec["local_error_cleared"] = local_cleared(target, c, span_first, first)
        rec["full_replay"] = c["kind"]
        rec["result"] = "full_replay_valid" if c["kind"] == "valid" else (
            "original_error_cleared_full_replay_failed" if rec["local_error_cleared"] and c["kind"] == "invalid" else "failed")
        attempts.append(rec)
        if c["kind"] == "valid":
            success = {"op": rec, "body": new_body, "check": c}
            break
    return attempts, success


def local_cleared(target, c, span_first, first):
    """True if no error remains at the originally failing position/span start."""
    for e in c["errors_in_target"]:
        if e["line"] == first["line"] or e["line"] == span_first:
            return False
    return True


def summarize_check(c):
    fe = c["first_error"]
    return {"kind": c["kind"], "exit_code": c["exit_code"], "axioms": c["axioms"],
            "n_errors_in_target": len(c["errors_in_target"]),
            "first_error": None if fe is None else {"line": fe["line"], "col": fe["col"],
                                                     "message": fe["message"][:1500]},
            "errors_outside_target": len(c["errors_outside_target"]), "run": c["run"],
            "wall_s_local": c["wall_s_local"]}


# ---------------------------------------------------------------- valid-path extraction / measurement

AUTO_RE = re.compile(r"^(\s*)([·.]\s+)?(simp_all|simp|aesop)(\s|$)")


def extract_valid(target, body, outdir, limit=3):
    """For a VALID body, replace bare simp/simp_all/aesop tactics with their `?` form one at a time."""
    lines = body.split("\n")
    out = []
    for i, line in enumerate(lines):
        if len(out) >= limit:
            break
        m = AUTO_RE.match(line)
        if not m or " only" in line or "?" in line:
            continue
        tac = m.group(3)
        if tac == "aesop" and not PROJECTS[target.project]["has_aesop"]:
            continue
        q = line.replace(tac, tac + "?", 1)
        trial = "\n".join(lines[:i] + [q] + lines[i + 1:])
        stem = outdir / f"extract_{i:03d}_{tac}Q"
        c = verify(target, trial, stem)
        res = jload(str(stem) + ".result.json")
        abs_line = target.body_first_line + i
        sugg, d = suggestion_in(res, abs_line, abs_line)
        rec = {"body_line": i, "original_line": line, "query_line": q, "query_check": summarize_check(c),
               "raw_tool_output": d["message"] if d else None, "suggestion": sugg}
        if sugg:
            new_body = "\n".join(replace_span(lines, i, i + 1, sugg))
            (outdir / f"extract_{i:03d}_{tac}Q_substituted.body.txt").write_text(new_body, encoding="utf-8")
            c2 = verify(target, new_body, outdir / f"extract_{i:03d}_{tac}Q_substituted")
            rec["substituted_body"] = new_body
            rec["substituted_check"] = summarize_check(c2)
        out.append(rec)
    return out


HB_ELAB = """open Lean Elab Command in
elab "#vm_count_heartbeats " "in" ppLine cmd:command : command => do
  let start ← IO.getNumHeartbeats
  try
    elabCommand (← `(command| set_option Elab.async false in set_option maxHeartbeats 0 in $cmd))
  finally
    let finish ← IO.getNumHeartbeats
    logInfo m!"VM_HEARTBEATS {(finish - start) / 1000}"

"""


def measure(target, body, stem):
    m = {"body_nonwhitespace_chars": {"value": len(re.sub(r"\s", "", body)), "kind": "local_estimate",
                                      "note": "character count, NOT the official token count"},
         "official_tokens": {"value": None, "kind": "not_measured", "reason": "official tokenizer not available"}}
    text = (target.source[:target.decl_start] + HB_ELAB + "#vm_count_heartbeats in\n"
            + target.source[target.decl_start:target.body_start] + body + target.suffix)
    res = run_lean(target.project, text, stem)
    hb = None
    errs = [d for d in res["diagnostics"] if d["severity"] == "error"]
    for d in res["diagnostics"]:
        mm = re.search(r"VM_HEARTBEATS (\d+)", d["message"])
        if mm:
            hb = int(mm.group(1))
    ok = hb is not None and not errs
    m["heartbeats"] = {"value": hb if ok else None, "kind": "local_estimate" if ok else "not_measured",
                       "method": "instrumented run: IO.getNumHeartbeats delta /1000 around the declaration with "
                                 "Elab.async=false (same mechanism as Mathlib #count_heartbeats); single run; "
                                 "not the official Arena measurement",
                       "run": rel(str(stem) + ".result.json"),
                       **({} if ok else {"reason": "instrumented run had errors or no output"})}
    return m


# ---------------------------------------------------------------- policy request

def context_excerpt(target, n_before=25):
    pre_lines = target.source[:target.decl_start].split("\n")
    keep = [l for l in pre_lines if re.match(r"^(import|open|namespace|section|end|variable|set_option)\b", l)]
    tail = pre_lines[-n_before:]
    return ("-- [harness] imports/open/namespace lines of the prefix:\n" + "\n".join(keep)
            + f"\n-- [harness] TRUNCATED: full prefix is {len(pre_lines)} lines ({target.spec['source']}); "
              f"only the last {n_before} lines before the declaration follow\n" + "\n".join(tail))


def build_request(case, target, status, candidate_body, diagnostics, localization, local_state, local_evidence,
                  baseline_ok, metrics=None, budget_variant="unpriced"):
    env = env_for(target.project)
    budget = {"cap_usd": None, "spent_usd": 0.0, "reserved_usd": 0.0, "next_call_upper_bound_usd": None,
              "source": "no price table / model selected; spent=0 is observed (no API call made)"}
    if budget_variant == "configured":
        budget = {"cap_usd": 3.0, "spent_usd": 0.0, "reserved_usd": 0.0, "next_call_upper_bound_usd": 0.30,
                  "source": "CONFIGURED PLACEHOLDER, not a price quote and not a Lean measurement"}
    x = {
        "problem_id": f"{case['id']}:{case['seed_id']}",
        "status": status,
        "baseline_verified": baseline_ok,
        "environment": {k: env[k] for k in ("lean_version", "lean_toolchain", "repo_commit", "lake_manifest_sha256")},
        "environment_hash": env["environment_hash"],
        "statement": case["statement"],
        "context": context_excerpt(target),
        "original_proof": target.original_body,
        "candidate_proof": candidate_body,
        "candidate_hash": sha(candidate_body),
        "diagnostics": diagnostics,
        "localization": localization,
        "local": {"state": local_state, "evidence": local_evidence},
        "llm_history": [],
        "limits": {"repair_requests": 2, "optimization_requests": 1},
        "budget": budget,
        "constraints": ["Body only: statement, binders, imports and surrounding declarations are fixed",
                        "No sorry/admit/new axioms/new declarations/self-reference",
                        "Same body must pass every listed version"],
        "source_contract": {"original_source": target.source, "candidate_source": target.file_with(candidate_body),
                            "body_start": target.body_start, "body_end": target.body_end,
                            "offsets": "python character offsets computed by harness string search (not a Lean parser)"},
    }
    if metrics is not None:
        x["metrics"] = metrics
    return x


def decide_and_write(cdir, req, suffix=""):
    jdump(req, cdir / f"request{suffix}.json")
    dec = escalation_policy.decide(req)
    jdump(dec, cdir / f"decision{suffix}.json")
    if dec["action"] == "EMIT_LLM_PROMPT":
        (cdir / f"prompt{suffix}.txt").write_text(dec["prompt"], encoding="utf-8")
    return dec


# ---------------------------------------------------------------- case driver

def apply_edits(body, edits):
    for e in edits:
        old, new = e[0], e[1]
        if len(e) > 2 and e[2] == "all":
            assert body.count(old) >= 1, f"edit anchor absent: {old!r}"
        else:
            assert body.count(old) == 1, f"edit anchor not unique/absent: {old!r}"
        body = body.replace(old, new)
    return body


def unified(a, b, name_a, name_b):
    return "".join(difflib.unified_diff(a.splitlines(True), b.splitlines(True), name_a, name_b))


def run_case(cid):
    from case_specs import CASES
    case = dict(CASES[cid])
    case["id"] = cid
    target = Target(case)
    cdir = HERE / "cases" / cid
    logs, attempts_dir = cdir / "logs", cdir / "attempts"
    for d in (logs, attempts_dir):
        d.mkdir(parents=True, exist_ok=True)
        for f in d.iterdir():
            f.unlink()
    print(f"[{cid}] baseline", flush=True)
    base = verify(target, target.original_body, logs / "00_baseline")
    baseline_ok = base["kind"] == "valid"

    cand = apply_edits(target.original_body, case["mutation"])
    (cdir / "original.lean").write_text(target.source, encoding="utf-8")
    (cdir / "candidate.lean").write_text(target.file_with(cand), encoding="utf-8")
    (cdir / "mutation.diff").write_text(unified(target.original_body, cand, "original_body", "candidate_body"),
                                        encoding="utf-8")

    print(f"[{cid}] candidate", flush=True)
    cc = verify(target, cand, logs / "01_candidate")
    state, state_reason = (None, "candidate valid")
    if cc["kind"] == "invalid":
        print(f"[{cid}] state capture", flush=True)
        state, state_reason = capture_state(target, cand, cc["first_error"], logs / "02_trace_state")

    attempts, success, extraction = [], None, []
    if cc["kind"] == "invalid":
        print(f"[{cid}] local repair", flush=True)
        attempts, success = local_repair(target, cand, cc["first_error"], attempts_dir)
    elif cc["kind"] == "valid":
        print(f"[{cid}] extraction on valid candidate", flush=True)
        extraction = extract_valid(target, cand, attempts_dir)

    # gold: written by the author independently of the local algorithm; alternatives in order
    print(f"[{cid}] gold", flush=True)
    gold_attempts, gold, gc = [], None, None
    for k, edits in enumerate(case["gold_alternatives"]):
        g = apply_edits(cand, edits)
        c = verify(target, g, logs / f"03_gold_alt{k}")
        gold_attempts.append({"alternative": k, "edits": [list(e) for e in edits], "check": summarize_check(c)})
        if gold is None or c["kind"] == "valid":
            gold, gc = g, c
        if c["kind"] == "valid":
            break
    (cdir / "gold_repair.lean").write_text(target.file_with(gold), encoding="utf-8")
    (cdir / "gold_repair.diff").write_text(unified(cand, gold, "candidate_body", "gold_body"), encoding="utf-8")

    # measurements: only where measurable
    print(f"[{cid}] measurements", flush=True)
    meas = {"baseline": measure(target, target.original_body, logs / "04_measure_baseline")}
    if cc["kind"] == "valid":
        meas["candidate"] = measure(target, cand, logs / "04_measure_candidate")
        for k, e in enumerate(extraction):
            if e.get("substituted_check", {}).get("kind") == "valid":
                meas[f"extracted_{k}"] = measure(target, e["substituted_body"], logs / f"04_measure_extracted_{k}")
    if success:
        meas["local_repair"] = measure(target, success["body"], logs / "04_measure_local_repair")
    if gc["kind"] == "valid" and gold != cand:
        meas["gold"] = measure(target, gold, logs / "04_measure_gold")
    versions = case["listed_versions"]
    available = case["available_versions"]
    meas["robustness"] = {"listed_versions": versions, "checked_versions": available,
                          "complete": bool(versions) and set(versions) <= set(available),
                          "note": case.get("version_note", "")}

    # localization (text heuristic; no parser)
    first = cc["first_error"]
    if first is not None:
        bl = body_line_of(target, first)
        line_txt = cand.split("\n")[bl] if 0 <= bl < len(cand.split("\n")) else ""
        if bl <= 0:
            scope = "body"
        elif first["message"].startswith("unsolved goals") or line_txt.strip().startswith(("case ", "next ")):
            scope = "block"
        else:
            scope = "tactic"
        localization = {"scope": scope, "file_line": first["line"], "col": first["col"], "body_line": bl,
                        "line_text": line_txt, "method": "text heuristic on first error position (not a parser)",
                        "trusted_pre_state": False}
    else:
        localization = {"scope": "body", "method": "no error", "trusted_pre_state": False}

    # policy request for the state reached after local work
    diag_out = [{"severity": d["severity"], "file_line": d["line"], "col": d["col"],
                 "body_line": None if d["line"] is None else d["line"] - target.body_first_line,
                 "message": d["message"]} for d in cc["errors_in_target"] + cc["errors_outside_target"]]
    evidence = [{k: a.get(k) for k in ("n", "op", "tactic", "result", "reason", "suggestion", "full_replay")}
                for a in attempts]
    if cc["kind"] == "invalid" and success is None:
        req = build_request(case, target, "invalid", cand, diag_out, localization, "exhausted",
                            evidence or ["no op applicable"], baseline_ok)
        if state:
            req["observed_pre_error_state_untrusted"] = state
    elif cc["kind"] == "invalid" and success is not None:
        req = build_request(case, target, "valid", success["body"], [], {"scope": "body", "trusted_pre_state": False},
                            "exhausted", evidence, baseline_ok)
        req["note"] = "candidate_proof is the locally repaired body after full replay; original candidate in case.json"
    elif cc["kind"] == "valid":
        ev = [{k: e.get(k) for k in ("body_line", "query_line", "suggestion")} |
              {"substituted": e.get("substituted_check", {}).get("kind")} for e in extraction]
        req = build_request(case, target, "valid", cand, [], {"scope": "body", "trusted_pre_state": False},
                            "exhausted" if extraction else "not_applicable",
                            ev or ["no bare simp/simp_all/aesop line to extract in a supported environment"],
                            baseline_ok)
    else:
        req = build_request(case, target, "environment_error", cand, diag_out, localization, "not_applicable",
                            [f"candidate run classified {cc['kind']}"], baseline_ok)
    dec = decide_and_write(cdir, req)
    dec_cfg = None
    if dec["action"] == "PRICE_REQUEST":
        dec_cfg = decide_and_write(cdir, build_request_variant(req), ".configured_budget")
    # move the configured prompt to prompt.txt (documented in README) when it exists
    if (cdir / "prompt.configured_budget.txt").exists():
        (cdir / "prompt.configured_budget.txt").rename(cdir / "prompt.txt")

    observed = cc["kind"]
    if success:
        route = "local_success"
    elif cc["kind"] == "invalid":
        route = "escalate_after_local_exhausted"
    elif cc["kind"] == "valid":
        route = "valid_measure_then_select"
    else:
        route = "fix_environment"
    case_json = {
        "id": cid, "seed_id": case["seed_id"], "source_kind": case["source_kind"],
        "source_path": case["source_origin"], "decl_full_name": case["full_name"],
        "environment": env_for(target.project) | {"project": target.project},
        "immutable_context_hash": target.immutable_context_hash(),
        "statement": case["statement"],
        "original_body": target.original_body, "original_body_sha256": sha(target.original_body),
        "body_range": {"body_start_char": target.body_start, "body_end_char": target.body_end,
                       "body_first_line": target.body_first_line, "decl_first_line": target.decl_first_line},
        "candidate_body": cand, "candidate_hash": sha(cand),
        "expected_intent": case["expected_intent"],
        "baseline_check": summarize_check(base),
        "observed_result": observed,
        "candidate_check": summarize_check(cc),
        "diagnostics": diag_out,
        "pre_error_state": state, "pre_error_state_null_reason": state_reason if state is None else None,
        "inferred_state": case.get("inferred_state"),
        "localization": localization,
        "local_attempts": attempts,
        "local_result": None if success is None else {"op": success["op"]["op"], "tactic": success["op"]["tactic"],
                                                       "body": success["body"], "check": summarize_check(success["check"])},
        "valid_path_extraction": extraction,
        "gold_repair_path": "gold_repair.lean",
        "gold_strategy": case["gold_strategy"],
        "gold_check": summarize_check(gc),
        "gold_attempts": gold_attempts,
        "full_replay_result": (success and summarize_check(success["check"])) or summarize_check(gc),
        "full_replay_result_source": "local_repair" if success else "gold_repair",
        "measurements": meas,
        "expected_route": route,
        "expected_route_reason": route_reason(route, cc, success, attempts),
        "author_prediction_before_run": case.get("prediction"),
        "policy_decision": {"decision.json": dec["action"],
                            "decision.configured_budget.json": dec_cfg["action"] if dec_cfg else None},
        "validation_status": validation_status(base, cc, gc, success, case),
    }
    jdump(case_json, cdir / "case.json")
    print(f"[{cid}] done: observed={observed} route={route} decision={dec['action']}"
          f"{' / ' + dec_cfg['action'] if dec_cfg else ''} gold={gc['kind']}", flush=True)
    return case_json


def build_request_variant(req):
    r = json.loads(json.dumps(req))
    r["budget"] = {"cap_usd": 3.0, "spent_usd": 0.0, "reserved_usd": 0.0, "next_call_upper_bound_usd": 0.30,
                   "source": "CONFIGURED PLACEHOLDER, not a price quote and not a Lean measurement"}
    return r


def route_reason(route, cc, success, attempts):
    if route == "local_success":
        return (f"fixed local op {success['op']['op']}({success['op']['tactic']}) made the whole file valid on full "
                f"replay; no LLM prompt expected")
    if route == "escalate_after_local_exhausted":
        partial = [a["n"] for a in attempts if a.get("result") == "original_error_cleared_full_replay_failed"]
        s = "all applicable local-ops-v1 attempts failed on full replay"
        if partial:
            s += f"; ops {partial} cleared the original error locally but full replay still failed"
        return s + "; no replay certificate so policy widens scope to body"
    if route == "valid_measure_then_select":
        return "candidate valid; official tokens not measured -> policy MEASURE before any optimization request"
    return f"candidate run classified {cc['kind']}"


def validation_status(base, cc, gc, success, case):
    if base["kind"] != "valid":
        return "BLOCKED_BASELINE"
    if cc["kind"] in ("environment_error", "context_error", "timeout"):
        return "BLOCKED_ENVIRONMENT"
    parts = ["lean_observed"]
    parts.append("gold_verified" if gc["kind"] == "valid" else f"gold_{gc['kind']}")
    parts.append("string_contract_only_no_lean_adapter_term_check")
    if not set(case["listed_versions"]) <= set(case["available_versions"]) or not case["listed_versions"]:
        parts.append("robustness_incomplete")
    return "+".join(parts)


# ---------------------------------------------------------------- policy-only commands

def rerender():
    for cdir in sorted((HERE / "cases").iterdir()):
        for req in sorted(cdir.glob("request*.json")):
            suffix = req.stem[len("request"):]
            dec = escalation_policy.decide(jload(req))
            jdump(dec, cdir / f"decision{suffix}.json")
            print(cdir.name, suffix or "(primary)", dec["action"], dec.get("scope"))


def fixtures():
    from policy_fixture_check import check_all
    sys.exit(0 if check_all(HERE / "policy-fixtures") else 1)


def write_manifest():
    from case_specs import CASES
    cases = {}
    for cid in sorted(CASES):
        p = HERE / "cases" / cid / "case.json"
        if p.exists():
            c = jload(p)
            cases[cid] = {k: c[k] for k in ("seed_id", "source_kind", "source_path", "observed_result",
                                            "expected_route", "policy_decision", "validation_status")}
    m = {
        "name": "validation-mini",
        "created": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "generator": "Antigravity agent (Claude Opus) acting on gemini-validation-data-request.md; no model API used "
                     "inside the harness",
        "pipeline": {
            "escalation_policy.py_sha256": file_sha(HERE.parent / "escalation_policy.py"),
            "escalation-policy-and-data-recipe.md_sha256": file_sha(HERE.parent / "escalation-policy-and-data-recipe.md"),
            "reproduce.py_sha256": file_sha(HERE / "reproduce.py"),
            "case_specs.py_sha256": file_sha(HERE / "case_specs.py"),
            "note": "No implemented Lean pipeline/local tactic list existed in the repository; local-ops-v1 below "
                    "was defined by this harness and frozen before the first case run. Not changed afterwards.",
        },
        "local_policy": LOCAL_POLICY_V1,
        "resource_settings": {"timeout_s_per_lean_run": TIMEOUT_S, "maxHeartbeats": "project default (not changed)",
                              "parallelism": "sequential runs"},
        "environments": jload(HERE / "environment.json"),
        "data_sources": {
            "arena_warmup": {"file": "~/lean_project/refactor_arena/benchmark_data_warmup.jsonl",
                             "copied_records": "sources/warmup_seeds_1_3.jsonl (lines 1-3)",
                             "sha256_of_full_file": "6209680cf00cde0765b77b24834cd72c64dd585b2f7e3f2a58209980ab59a804",
                             "line_number_note": "dataset start_line values (2964/2733/950) differ from the git HEAD "
                                                 "file positions (3089/2858/931); declarations were located by exact "
                                                 "text match of `src` (unique)"},
            "strata_sources": {f.name: file_sha(f) for f in sorted((HERE / "sources").glob("strata_*.lean"))},
            "toy_sources": {f.name: file_sha(f) for f in sorted((HERE / "sources/toy").glob("*.lean"))},
        },
        "cases": cases,
        "policy_fixtures": "policy-fixtures/ (synthetic=true; generated by make_policy_fixtures.py)",
    }
    jdump(m, HERE / "manifest.json")
    print(json.dumps(cases, indent=1))


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "help"
    if cmd == "env":
        e = environment_record()
        jdump(e, HERE / "environment.json")
        print(json.dumps(e, indent=2))
    elif cmd == "case":
        for c in sys.argv[2:]:
            run_case(c)
    elif cmd == "all":
        from case_specs import CASES
        for c in sorted(CASES):
            run_case(c)
    elif cmd == "policy":
        rerender()
    elif cmd == "manifest":
        write_manifest()
    elif cmd == "fixtures":
        fixtures()
    else:
        print(__doc__)
