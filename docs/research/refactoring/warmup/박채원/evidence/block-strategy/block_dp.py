#!/usr/bin/env python3
"""Compile-checked block candidates and tree DP selection (proof tokens only).

Rules (designed with 박채원; no LLM; the same input always gives the same output)
  5. Priority queue: candidates are tried in decreasing order of their upper
     bound (exact groups: (count - 1) * block tokens; removals: block tokens).
  6. Memoisation: every compiled text is cached by its SHA-1, so the same
     file is never compiled twice (cache.json in the output folder).
  7. Tree DP: on the block tree, the best value of a node is the larger of
     (a) the sum of its children's best values and (b) for each candidate
     attached to the node, its measured gain plus the best values of the parts
     of the subtree it does not touch. Candidates never overlap in the chosen
     set. The chosen set is applied together and compiled again; the predicted
     total gain is compared with the measured one.

Candidate sources (rule 8 added: identical branch bodies)
  A. Unused `have` removal from prune_unused.py results: each first-pass block
     on its own, and the whole pruning result as one candidate (later passes
     depend on earlier ones).
  B. Exact duplicate group -> one generalised lemma. The first member becomes
     `have gen : ∀ (params), STMT := by intro params; <its proof>` followed by
     `have NAME := gen params`; the other members become `have NAME := gen args`.
     Parameters are the names that differ between members and exist in the
     local context before the first member (read with `trace_state`); their
     types are taken from that context. Groups whose differences are not all
     context names or locally bound names are skipped and listed.

Objective: official proof_length reduction. heartbeat is not used.

usage:
  # standalone mode: benchmark header (import Mathlib) + declaration in a lake project
  python block_dp.py --jsonl benchmark_data_warmup.jsonl --row 15 --project project \
      --prune results/prune15 --out results/dp15
  # file mode: replace the declaration inside the row's repository file (version_info
  # commit, built) and compile with `lake lean`; the file is restored byte for byte
  python block_dp.py --jsonl benchmark_data_warmup.jsonl --row 10 --repo <ArkLib checkout> \
      --prune results/prune10 --out results/dp10
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "block-analyzer"))
sys.path.insert(0, os.path.join(HERE, "..", "local-v4.26", "tools"))
from proof_tokens import proof_length  # noqa: E402
from block_analyzer import strip_comments_keep_lines, line_tokens, indent, normalise  # noqa: E402
import block_tree as BT  # noqa: E402

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
BASE_AXIOMS: set = set()     # axioms of the reference proof, filled after the base compile
CACHE_VERSION = "2"          # bump when the parsing of compile results changes
HEADER_RE = re.compile(r"^(\s*)have\s+(\S+)\s*:\s*(.+?)\s*:=\s*by\s*$")
BINDER_RE = re.compile(r"\b(?:have|let|set|intro|intros|fun|obtain|rcases|rintro|cases|induction)\b(.*)")
IDENT_RE = re.compile(r"[^\W\d][\w'₀-₉!?]*")


# ---------- compile with memoisation (rule 6) ----------
class Compiler:
    def __init__(self, project, workdir, timeout, target=None, rel=None):
        self.project, self.workdir, self.timeout, self.target = project, workdir, timeout, target
        self.rel = rel
        self.path = os.path.join(workdir, "cache.json")
        self.cache = json.load(open(self.path, encoding="utf-8")) if os.path.exists(self.path) else {}
        self.hits = self.runs = 0

    def run(self, text, tag):
        key = hashlib.sha1((CACHE_VERSION + text).encode()).hexdigest()
        if key in self.cache:
            self.hits += 1
            return self.cache[key]
        self.runs += 1
        f = os.path.abspath(os.path.join(self.workdir, f"{tag}.lean"))
        open(f, "w", encoding="utf-8", newline="\n").write(text)
        if self.target:              # file mode: compile in place inside the repository
            open(self.target, "w", encoding="utf-8", newline="\n").write(text)
            f = self.target
        # file mode: `lake lean` applies the library's own options (leanOptions / moreLeanArgs)
        cmd = (["lake", "lean", self.rel, "--", "--json"] if self.target
               else ["lake", "env", "lean", "--json", f])
        p = subprocess.run(cmd, cwd=self.project,
                           capture_output=True, text=True, encoding="utf-8", errors="replace",
                           timeout=self.timeout)
        msgs = []
        for ln in p.stdout.splitlines():
            try:
                msgs.append(json.loads(ln))
            except json.JSONDecodeError:
                pass
        errors = sum(m.get("severity") == "error" for m in msgs)
        if p.returncode != 0 and errors == 0:      # e.g. a Lake-level failure printed as plain text
            errors = 1
        ax = None
        for m in msgs:
            mm = re.search(r"depends on axioms: \[(.*?)\]", m.get("data", ""), re.S)   # list may wrap
            if mm:
                ax = [a.strip() for a in mm.group(1).split(",") if a.strip()]
        res = {"errors": errors, "axioms": ax,
               "traces": [{"line": m["pos"]["line"], "data": m["data"]} for m in msgs if m.get("kind") == "trace"],
               "first_error": next((m["data"][:300] for m in msgs if m.get("severity") == "error"), None)}
        self.cache[key] = res
        json.dump(self.cache, open(self.path, "w", encoding="utf-8"), ensure_ascii=False)
        return res


def ok(res):
    return (res["errors"] == 0 and res["axioms"] is not None
            and set(res["axioms"]) <= ALLOWED_AXIOMS | BASE_AXIOMS)


# ---------- helpers ----------
FILE_CTX = None   # file mode: (text before the declaration, text after it), set in main()


def file_text(header, decl, name, extra=""):
    if FILE_CTX is not None:   # file mode: keep the repository file around the declaration
        head, doc, after = FILE_CTX
        # options go above the doc comment (an `in` between a doc comment and the declaration does not parse)
        pre = head + "".join(l + "\n" for l in extra.split("\n") if l.strip()) + doc
        return pre + decl.rstrip("\n") + f"\n\n#print axioms {name}\n" + after, pre.count("\n")
    pre = header.rstrip("\n") + "\n" + extra + "\n"
    return pre + decl.rstrip("\n") + f"\n\n#print axioms {name}\n", pre.count("\n")


def locate_decl(lines, row):
    """0-based [s0, e0) of the declaration in the file. Uses the row's start/end lines when
    they match the source text; otherwise finds the unique exact occurrence of the source."""
    s0, e0 = row["start_line"] - 1, row["end_line"]
    src = row["src"].rstrip("\n")
    if "\n".join(lines[s0:e0]).rstrip("\n") == src:
        return s0, e0
    text = "\n".join(lines)
    i = text.find(src)
    if i < 0 or text.find(src, i + 1) >= 0:
        raise SystemExit("declaration source not found exactly once in " + row["file_path"])
    s0 = text.count("\n", 0, i)
    return s0, s0 + src.count("\n") + 1


def decl_head_start(lines, s0):
    """First line of the doc comment / attributes / `… in` prefixes attached to the declaration at s0.
    Options are inserted above them so the doc comment stays attached to the declaration."""
    j = s0
    while j > 0:
        k = j - 1
        if lines[k].lstrip().startswith("@[") or lines[k].rstrip().endswith(" in"):   # attributes, `omit … in` etc.
            j = k
            continue
        if lines[k].rstrip().endswith("-/"):
            m = k
            while m >= 0 and "/-" not in lines[m]:
                m -= 1
            if m >= 0 and lines[m].lstrip().startswith("/--"):
                j = m
                continue
        break
    return j


def parse_ctx(trace):
    """Parse a trace_state goal into [(name, type)] in order."""
    out, cur = [], None
    for ln in trace.split("\n"):
        if ln.startswith("⊢") or ln.startswith("case "):
            break
        if ln and not ln[0].isspace() and " : " in ln:
            names, typ = ln.split(" : ", 1)
            cur = [names.split(), typ.strip()]
            out.append(cur)
        elif ln and not ln[0].isspace() and ln.endswith(" :"):
            cur = [ln[:-2].split(), ""]
            out.append(cur)
        elif cur is not None:
            cur[1] = (cur[1] + " " + ln.strip()).strip()
    res = []
    for names, typ in out:
        for n in names:
            res.append((n, typ))
    return res


def inner_bound(lines, idxs):
    """Names introduced inside a block (not free names it merely mentions)."""
    names = set()
    for i in idxs:
        t = lines[i].strip().lstrip("·").strip()
        m = re.match(r"(?:have|let|set|replace|suffices)\s+([^\s:(]+)", t)
        if m:
            names.add(m.group(1))
        m = re.match(r"(?:intro|intros|rintro)\s+(.*)", t)
        if m:
            names.update(IDENT_RE.findall(m.group(1)))
        for pat in re.findall(r"⟨([^⟩]*)⟩", t.split(":=")[0] if t.startswith("obtain") else
                              (t.split(" with ", 1)[1] if " with " in t else "")):
            names.update(IDENT_RE.findall(pat))
        for seg in re.findall(r"\bfun\s+(.*?)=>", t):
            names.update(IDENT_RE.findall(seg.split(":")[0]))
        m = re.match(r"(?:case\s+\S+|\|\s*\S+)\s+(.*?)=>", t)
        if m:
            names.update(IDENT_RE.findall(m.group(1)))
    names.discard("_")
    return names


def removed_lines(src_lines, final_lines):
    sm = difflib.SequenceMatcher(None, src_lines, final_lines, autojunk=False)
    gone = set()
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag in ("delete", "replace"):
            gone.update(range(i1, i2))
    return gone


# ---------- candidate B: exact group -> generalised lemma ----------
def lemma_candidate(k, group, src, clean, ctx, gen_name):
    A = group[0]
    hdr = [HEADER_RE.match(src[n.line]) for n in group]
    if not all(hdr):
        return None, "멤버의 첫 줄이 `have NAME : STMT := by` 한 줄 형식이 아님"
    toks = [n.toks for n in group]
    if len({len(t) for t in toks}) != 1:
        return None, "토큰 수가 다름"
    bound = inner_bound(clean, A.lines[1:])
    ctx_names = [n for n, _ in ctx]
    ctx_type = dict(ctx)
    maps = []
    for t in toks[1:]:
        mp = {}
        for a, b in zip(toks[0], t):
            if a != b:
                if mp.get(a, b) != b:
                    return None, f"이름 대응이 일관되지 않음 ({a})"
                mp[a] = b
        maps.append(mp)
    diff_names = set().union(*[set(m) for m in maps])
    hdr_name_a = hdr[0].group(2)
    params = [n for n in ctx_names if n in diff_names and n not in bound]
    other = [d for d in diff_names if d not in params and d not in bound and d != hdr_name_a]
    other = [d for d in other if not any(d == h.group(2) for h in hdr)]
    if other:
        return None, f"문맥 이름이 아닌 차이: {sorted(other)[:5]}"
    if not params:
        return None, "인자가 없음"
    ind = hdr[0].group(1)
    binders = " ".join(f"({p} : {ctx_type[p]})" for p in params)
    lines_a = [f"{ind}have {gen_name} : ∀ {binders}, {hdr[0].group(3)} := by",
               f"{ind}  intro {' '.join(params)}"]
    lines_a += [src[i] for i in range(A.line + 1, A.lines[-1] + 1)]
    lines_a.append(f"{ind}have {hdr_name_a} := {gen_name} {' '.join(params)}")
    repl = {tuple(range(A.line, A.lines[-1] + 1)): lines_a}
    for n, h, mp in zip(group[1:], hdr[1:], maps):
        args = " ".join(mp.get(p, p) for p in params)
        repl[tuple(range(n.line, n.lines[-1] + 1))] = [f"{h.group(1)}have {h.group(2)} := {gen_name} {args}"]
    return repl, None


def apply(src, repls):
    """repls: {tuple of line indices: new lines}. Each line set may be non-contiguous;
    its new lines are emitted at its first line and all its lines are dropped."""
    owner = {}
    for rng in repls:
        for i in rng:
            owner[i] = rng
    out = []
    for i, line in enumerate(src):
        rng = owner.get(i)
        if rng is None:
            out.append(line)
        elif i == min(rng):
            out += repls[rng]
    return out


# ---------- rule 8: identical branch bodies -> one branch with several tags ----------
CASE_RE = re.compile(r"^(\s*)case\s+(.+?)\s*=>\s*$")     # `case tag args =>` with the body below
ALT_RE = re.compile(r"^(\s*)\|\s*(.+?)\s*=>\s*$")         # `| pattern =>` alternative with the body below


def case_merge_candidate(group, src, clean):
    """Members are `case t =>` (or `| p =>`) blocks whose bodies are identical text.
    Lean accepts `case t1 | t2 => tac` and `| p1 | p2 => tac`, so the first member keeps
    its body under a merged head and the other members are deleted."""
    heads = [src[n.line] for n in group]
    for rx, kw in ((CASE_RE, "case "), (ALT_RE, "| ")):
        ms = [rx.match(h) for h in heads]
        if all(ms):
            break
    else:
        return None, None                                   # not a branch group
    if len({m.group(1) for m in ms}) != 1:
        return None, "분기 머리의 들여쓰기가 서로 다름"
    def body(n):
        return [clean[i].strip() for i in n.lines[1:] if clean[i].strip()]
    b0 = body(group[0])
    if not b0 or any(body(n) != b0 for n in group[1:]):
        return None, "분기 본문이 이름까지 똑같지는 않음"
    ind = ms[0].group(1)
    head = ind + kw + " | ".join(m.group(2) for m in ms) + " =>"
    repl = {(group[0].line,): [head]}
    for n in group[1:]:
        repl[tuple(n.lines)] = []
    return repl, None


# ---------- rule 7: tree DP ----------
def tree_dp(root, cands):
    """cands: list of dict(lines=set, gain=int, id=str). Returns (best, chosen ids)."""
    memo = {}

    def sub_lines(n):
        return set(n.lines)

    def lca_ok(n, c):
        return c["lines"] <= sub_lines(n) and not any(c["lines"] <= sub_lines(ch) for ch in n.children)

    attached = {}
    for c in cands:
        for n in BT.walk(root):
            if lca_ok(n, c):
                attached.setdefault(id(n), []).append(c)
                break

    def g(n, blocked):
        key = (id(n), blocked)
        if key in memo:
            return memo[key]
        S = sub_lines(n)
        if S and S <= set(blocked):
            memo[key] = (0, ())
            return memo[key]
        best_v, best_ids = 0, ()
        for ch in n.children:
            v, ids = g(ch, blocked)
            best_v += v; best_ids += ids
        here = [c for c in attached.get(id(n), []) if not (c["lines"] & set(blocked))]
        # every non-overlapping subset of the candidates attached to this node
        for mask in range(1, 1 << len(here)):
            pick = [here[b] for b in range(len(here)) if mask >> b & 1]
            used = set()
            if any(used & c["lines"] or used.update(c["lines"]) for c in pick):
                continue
            nb = frozenset(set(blocked) | used)
            v, ids = sum(c["gain"] for c in pick), tuple(c["id"] for c in pick)
            for ch in n.children:
                cv, cids = g(ch, nb)
                v += cv; ids += cids
            if v > best_v:
                best_v, best_ids = v, ids
        memo[key] = (best_v, best_ids)
        return memo[key]

    return g(root, frozenset())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jsonl", required=True)
    ap.add_argument("--row", type=int, required=True)
    ap.add_argument("--project", help="lake project for standalone mode")
    ap.add_argument("--repo", help="checked-out repository (version_info commit, built) for file mode")
    ap.add_argument("--header")
    ap.add_argument("--prune", help="prune_unused.py output folder for this row")
    ap.add_argument("--out", required=True)
    ap.add_argument("--timeout", type=int, default=1800)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    rows = [json.loads(l) for l in open(a.jsonl, encoding="utf-8") if l.strip()]
    row = rows[a.row - 1]
    global FILE_CTX
    if a.repo:
        target = os.path.abspath(os.path.join(a.repo, row["file_path"]))
        orig_bytes = open(target, "rb").read()
        lines = orig_bytes.decode("utf-8").replace("\r\n", "\n").split("\n")
        s0, e0 = locate_decl(lines, row)
        h0 = decl_head_start(lines, s0)
        FILE_CTX = ("".join(l + "\n" for l in lines[:h0]), "".join(l + "\n" for l in lines[h0:s0]),
                    "\n" + "\n".join(lines[e0:]))
        header, project = "", a.repo
        comp = Compiler(project, a.out, a.timeout, target, row["file_path"])
        try:
            run(a, row, header, comp)
        finally:
            open(target, "wb").write(orig_bytes)          # restore the repository file byte for byte
        return
    if not a.project:
        raise SystemExit("give --project (standalone) or --repo (file mode)")
    header = open(a.header, encoding="utf-8").read() if a.header else row["header"]
    comp = Compiler(a.project, a.out, a.timeout)
    run(a, row, header, comp)


def run(a, row, header, comp):
    src = row["src"].split("\n")
    clean = strip_comments_keep_lines(row["src"]).split("\n")
    base_tokens = proof_length(row["src"], row["statement"])

    # tree (rules 1-2) and exact groups (rule 3) from block_tree.py
    text = strip_comments_keep_lines(row["src"])
    pos = text.index(":=", len(strip_comments_keep_lines(row["statement"]))) + 2
    first = text.count("\n", 0, pos)
    body = [i for i in range(first + 1, len(clean)) if clean[i].strip()]
    root = BT.build_tree(clean, body)
    BT.dfs(root)
    res_tree = BT.analyse(row)
    nodes = [n for n in BT.walk(root) if n.line >= 0]
    by_line = {n.line: n for n in nodes}
    groups = [[by_line[m[0] - 1] for m in g["members"]] for g in res_tree["exact_groups"]]

    base = comp.run(file_text(header, row["src"], row["name"])[0], "base")
    if base["errors"] == 0 and base["axioms"] is not None:
        BASE_AXIOMS.update(base["axioms"])
    if not ok(base):
        raise SystemExit(f"reference does not compile: {base['first_error']}")

    cands, skipped, log = [], [], []
    # candidate A: unused-have removal
    if a.prune:
        final = open(os.path.join(a.prune, "final.lean"), encoding="utf-8").read().rstrip("\n").split("\n")
        gone = removed_lines(src, final)
        if gone:
            cands.append({"id": "prune_all", "kind": "미사용 have 제거(전체)", "lines": set(gone),
                          "gain": base_tokens - proof_length("\n".join(final), row["statement"]),
                          "repl": {tuple(sorted(gone)): []}, "verified": "prune_unused.py 결과"})
        p1 = json.load(open(os.path.join(a.prune, "result.json")))["passes"]
        p1_names = p1[1]["removed"] if len(p1) > 1 else []
        for n in nodes:
            if set(n.lines) <= gone and (n.parent.line < 0 or not set(n.parent.lines) <= gone):
                m = HEADER_RE.match(src[n.line]) or re.match(r"^\s*(?:·\s*)?(?:have|obtain|let|set)\s+(\S+)", src[n.line])
                nm = m.group(2) if m and m.re is HEADER_RE else (m.group(1) if m else "")
                if nm in p1_names:
                    rng = tuple(n.lines)
                    cands.append({"id": f"prune_{n.line + 1}", "kind": f"미사용 have 제거 ({nm})",
                                  "lines": set(n.lines), "gain": n.sub, "repl": {rng: []},
                                  "verified": "1회차 제거 블록(단독 유효)"})
    # candidate B: exact groups -> lemma, tried in priority-queue order (rule 5)
    order = sorted(range(len(groups)), key=lambda i: -(len(groups[i]) - 1) * groups[i][0].sub)
    for gi in order:
        g = groups[gi]
        tag = f"group{gi + 1}"
        # rule 8: identical branch bodies (no context needed)
        repl, why = case_merge_candidate(g, src, clean)
        if repl is not None or why is not None:
            if repl is None:
                skipped.append({"group": tag, "lines": [n.line + 1 for n in g], "reason": why})
                continue
            new = "\n".join(apply(src, repl))
            r = comp.run(file_text(header, new, row["name"])[0], tag)
            toks = proof_length(new, row["statement"])
            gain = base_tokens - toks
            log.append({"group": tag, "kind": "분기 합치기", "lines": [n.line + 1 for n in g],
                        "compiles": ok(r), "tokens": toks, "gain": gain, "error": r["first_error"]})
            if ok(r) and gain > 0:
                lines = set().union(*[set(n.lines) for n in g])
                cands.append({"id": tag, "kind": f"같은 본문의 분기 {len(g)}개 → 하나로", "lines": lines,
                              "gain": gain, "repl": repl, "verified": "단독 컴파일 통과"})
            continue
        probe = list(src)
        A = g[0]
        probe.insert(A.line, " " * indent(src[A.line]) + "trace_state")
        pr = comp.run(file_text(header, "\n".join(probe), row["name"],
                                "set_option pp.deepTerms true\nset_option pp.proofs true\n")[0], f"{tag}_ctx")
        traces = pr["traces"]
        if not traces:
            skipped.append({"group": tag, "lines": [n.line + 1 for n in g], "reason": "문맥을 읽지 못함"})
            continue
        ctx = parse_ctx(traces[0]["data"])
        repl, why = lemma_candidate(gi, g, src, clean, ctx, f"blk_gen{gi + 1}")
        if repl is None:
            skipped.append({"group": tag, "lines": [n.line + 1 for n in g], "reason": why})
            continue
        new = "\n".join(apply(src, repl))
        r = comp.run(file_text(header, new, row["name"])[0], tag)
        toks = proof_length(new, row["statement"])
        gain = base_tokens - toks
        log.append({"group": tag, "lines": [n.line + 1 for n in g], "compiles": ok(r), "tokens": toks,
                    "gain": gain, "error": r["first_error"]})
        if ok(r) and gain > 0:
            lines = set().union(*[set(n.lines) for n in g])
            cands.append({"id": tag, "kind": f"중복 {len(g)}개 → 보조정리", "lines": lines, "gain": gain,
                          "repl": repl, "verified": "단독 컴파일 통과"})

    best, chosen = tree_dp(root, cands)
    chosen_c = [c for c in cands if c["id"] in chosen]
    merged = {}
    for c in chosen_c:
        merged.update(c["repl"])
    final_lines = apply(src, merged) if merged else src
    final = "\n".join(final_lines)
    fr = comp.run(file_text(header, final, row["name"])[0], "combined")
    final_tokens = proof_length(final, row["statement"])
    open(os.path.join(a.out, "final.lean"), "w", encoding="utf-8").write(final + "\n")
    out = {"row_index": a.row, "row": row["name"], "start_tokens": base_tokens, "final_tokens": final_tokens,
           "predicted_gain": best, "measured_gain": base_tokens - final_tokens,
           "combined_compiles": ok(fr), "combined_error": fr["first_error"], "axioms": fr["axioms"],
           "candidates": [{k: (sorted(x + 1 for x in v) if k == "lines" else v) for k, v in c.items() if k != "repl"}
                          for c in cands],
           "chosen": list(chosen), "lemma_attempts": log, "skipped_groups": skipped,
           "compile_runs": comp.runs, "cache_hits": comp.hits,
           "header": ("file mode: " + row["file_path"]) if a.repo else (
               "custom: " + os.path.basename(a.header) if a.header else "benchmark header")}
    json.dump(out, open(os.path.join(a.out, "result.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print(json.dumps({k: out[k] for k in ("row", "start_tokens", "final_tokens", "predicted_gain",
                                          "measured_gain", "combined_compiles", "chosen")}, ensure_ascii=False))
    for l in log:
        print("  lemma", l["group"], l["lines"], "compiles" if l["compiles"] else "FAIL", l["tokens"], l["gain"],
              (l["error"] or "")[:120].replace("\n", " "))
    for s in skipped:
        print("  skip", s)


if __name__ == "__main__":
    main()
