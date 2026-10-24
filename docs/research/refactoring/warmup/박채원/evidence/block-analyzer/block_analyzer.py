#!/usr/bin/env python3
"""Split a Lean `by` proof into blocks and count official proof tokens per block.

Tokens follow `proof_length` (Lean Refactor paper, Appendix J) through
proof_tokens.py, which reproduces the official value of all 15 warm-up rows.
Because proof_length sums per line, block counts plus the tokens on the
`:= by` line add up to the official total; every run checks this.

Block rule
  1. A block is one tactic at the proof's base indentation together with the
     more-indented lines under it (a `have ... := by` and its proof, a `·`
     bullet, a `calc`, ...).
  2. Wrapper descent: if one block holds at least WRAP_SHARE of the tokens
     and has nested lines, its nested lines are split again; the wrapper's
     own header line(s) become a separate "wrapper" entry.
  3. Repeated-argument candidates: every nested block with at least
     MIN_DUP tokens (at any depth) is alpha-normalised (local names replaced
     by placeholders in order of appearance) and compared pairwise; pairs
     with similarity >= DUP_RATIO are listed. This is a candidate list, not
     a proof of equivalence.
  5. Proof type: the block kind (case branch, calc step, have family) holding
     at least TYPE_SHARE of the tokens names the type; blocks holding at least
     EXPAND_SHARE are split one more level with the same indentation rule.
  4. Case-body candidates: bodies of `case tag =>` and `| tag =>` alternatives
     with at least MIN_CASE tokens are compared the same way (ratio >=
     CASE_RATIO). Proofs by induction/cases (Strata, CSLib) repeat at this
     smaller scale.

usage (from this folder; proof_tokens.py is read from ../local-v4.26/tools):
  python block_analyzer.py benchmark_data_warmup.jsonl            # all rows
  python block_analyzer.py benchmark_data_warmup.jsonl --rows 1 15
  python block_analyzer.py benchmark_data_warmup.jsonl --json out.json --md out.md
"""
from __future__ import annotations

import argparse
import difflib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "local-v4.26", "tools"))
from proof_tokens import lex, remove_comments  # noqa: E402

WRAP_SHARE = 0.8
MIN_DUP = 40
DUP_RATIO = 0.9
MIN_CASE = 8
CASE_RATIO = 0.85
EXPAND_SHARE = 0.4   # blocks at least this share of the proof are split one level further
TYPE_SHARE = 0.5     # a proof type needs this share of tokens in one block kind
TYPE_NAMES = {"case": "분기형", "calc": "계산 연쇄형", "have": "중간 명제형", "mixed": "혼합형"}
TYPE_RULES = {
    "case": "`case`·`&#124; tag =>` 분기 하나를 블록으로 봄. 큰 분기 안의 분기(`cases` 안 `case`)는 한 단계 더 나눔. 분기 본문끼리 비교함.",
    "calc": "`calc`의 단계 하나(`_ = …`와 그 근거)를 블록으로 봄. 큰 `calc` 블록은 단계 단위로 한 단계 더 나눔.",
    "have": "`have` 하나와 그 증명을 블록으로 봄. 감싸는 `have`는 안으로 내려가고, 큰 `have`는 안쪽 `have` 단위로 한 단계 더 나눔. 사용되지 않는 `have`는 Lean 린터로 찾음.",
    "mixed": "들여쓰기 블록 규칙을 그대로 씀.",
}
KEYWORDS = set("""have show from by at with fun if then else let in match do calc exact
apply intro intros rw simp simp_all only obtain rcases cases induction use refine
constructor norm_num linarith nlinarith omega ring field_simp aesop decide rfl
unfold specialize generalize subst congr ext funext by_cases by_contra push_neg
exfalso contradiction trivial assumption split_ifs split case next all_goals any_goals
try first repeat convert positivity gcongr classical this Nat Int Real Finset Set
Fin Type Prop True False sorry fun_prop grind""".split())


def strip_comments_keep_lines(src: str) -> str:
    """Blank out comments but keep every newline so line numbers stay valid."""
    out, i, n, depth, in_str = [], 0, len(src), 0, False
    while i < n:
        two = src[i:i + 2]
        if depth:
            if two == "/-":
                depth, i = depth + 1, i + 2
                out.append("  ")
            elif two == "-/":
                depth, i = depth - 1, i + 2
                out.append("  ")
            else:
                out.append("\n" if src[i] == "\n" else " ")
                i += 1
        elif in_str:
            out.append(src[i])
            if src[i] == "\\" and i + 1 < n:
                out.append(src[i + 1]); i += 1
            elif src[i] == '"':
                in_str = False
            i += 1
        elif two == "/-":
            depth, i = 1, i + 2
            out.append("  ")
        elif two == "--":
            while i < n and src[i] != "\n":
                out.append(" "); i += 1
        else:
            in_str = src[i] == '"'
            out.append(src[i]); i += 1
    return "".join(out)


def line_tokens(line: str) -> list[str]:
    return lex(line.strip()).split(" ") if line.strip() else []


def indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def split_blocks(lines, idxs):
    """idxs: indices of non-empty lines forming one region. Returns list of index lists."""
    if not idxs:
        return []
    base = min(indent(lines[i]) for i in idxs)
    blocks, cur = [], []
    for i in idxs:
        if indent(lines[i]) == base and cur:
            blocks.append(cur); cur = []
        cur.append(i)
    if cur:
        blocks.append(cur)
    return blocks


def head(lines, i, width=70):
    t = " ".join(lines[i].split())
    return t if len(t) <= width else t[:width - 1] + "…"


def kind_name(lines, i):
    words = lines[i].split()
    if not words:
        return "", ""
    k = words[0]
    name = ""
    if k in ("have", "obtain", "let", "suffices", "replace") and len(words) > 1:
        name = words[1].rstrip(":")
    return k, name


def normalise(tokens):
    mp, out = {}, []
    for t in tokens:
        if (t[:1].isalpha() or t[:1] == "_") and "." not in t and t not in KEYWORDS:
            mp.setdefault(t, f"v{len(mp)}")
            out.append(mp[t])
        else:
            out.append(t)
    return out


def analyse(row):
    src, stmt = row["src"], row["statement"]
    clean_stmt = remove_comments(stmt)
    if not remove_comments(src).startswith(clean_stmt):
        raise ValueError("src does not start with statement")
    text = strip_comments_keep_lines(src)
    # locate ':=' after the statement in the comment-stripped text
    stmt_len = len(strip_comments_keep_lines(stmt))
    pos = text.index(":=", stmt_len) + 2
    first_line_no = text.count("\n", 0, pos)          # 0-based line holding ':='
    lines = text.split("\n")
    raw_lines = src.split("\n")
    head_tail = text[pos:].split("\n", 1)[0]            # e.g. ' by '
    head_tokens = len(line_tokens(head_tail))
    tok = {i: len(line_tokens(lines[i])) for i in range(first_line_no + 1, len(lines))}
    body = [i for i in range(first_line_no + 1, len(lines)) if lines[i].strip()]
    total = head_tokens + sum(tok[i] for i in body)

    def btok(b):
        return sum(tok[i] for i in b)

    entries, path = [], []
    region = body
    depth = 0
    while True:
        blocks = split_blocks(lines, region)
        big = max(blocks, key=btok)
        if (len(blocks) >= 1 and btok(big) >= WRAP_SHARE * total and len(big) > 1
                and any(indent(lines[j]) > indent(lines[big[0]]) for j in big[1:])):
            # descend into the wrapper: header lines = lines of `big` at its own indent
            # before the first deeper line
            others = [b for b in blocks if b is not big]
            for b in others:
                entries.append(("block", b, depth))
            hdr = [big[0]]
            rest = big[1:]
            entries.append(("wrapper", hdr, depth))
            depth += 1
            path.append(head(raw_lines, big[0], 40))
            region = rest
            continue
        for b in blocks:
            entries.append(("block", b, depth))
        break
    entries.sort(key=lambda e: e[1][0])
    out_blocks = []
    def kind_of(i):
        t = lines[i].strip()
        k0 = t.split()[0] if t.split() else ""
        if t.startswith(("case ", "| ", "next ")):
            return "case"
        if k0 in ("have", "obtain", "let", "suffices", "set", "replace"):
            return "have"
        if k0 == "calc" or t.startswith("_ "):
            return "calc"
        return "other"

    def children(b):
        inner = b[1:]
        if not inner:
            return []
        out = []
        for c in split_blocks(lines, inner):
            out.append({"first_line": c[0] + 1, "last_line": c[-1] + 1, "kind": kind_of(c[0]),
                        "head": head(raw_lines, c[0]), "tokens": btok(c),
                        "share": round(btok(c) / total * 100, 1)})
        return out

    for kind, b, dep in entries:
        k, name = kind_name(lines, b[0])
        out_blocks.append({
            "kind": kind_of(b[0]),
            "children": children(b) if kind == "block" and btok(b) >= EXPAND_SHARE * total and len(b) > 1 else [],
            "role": kind, "depth": dep, "first_line": b[0] + 1, "last_line": b[-1] + 1,
            "file_lines": [row.get("start_line", 1) + b[0], row.get("start_line", 1) + b[-1]],
            "tactic": k, "name": name, "head": head(raw_lines, b[0]),
            "tokens": btok(b), "share": round(btok(b) / total * 100, 1),
        })
    # repeated-argument candidates among nested blocks at any depth
    cands = []
    for i in body:
        nxt = [j for j in body if j > i]
        sub = [i]
        for j in nxt:
            if indent(lines[j]) > indent(lines[i]):
                sub.append(j)
            else:
                break
        if len(sub) > 1 and btok(sub) >= MIN_DUP:
            cands.append(sub)
    seqs = [normalise([t for i in s for t in line_tokens(lines[i])]) for s in cands]
    dups = []
    for a in range(len(cands)):
        for c in range(a + 1, len(cands)):
            A, C = cands[a], cands[c]
            if set(A) & set(C):
                continue  # nested or overlapping
            la, lc = len(seqs[a]), len(seqs[c])
            if min(la, lc) / max(la, lc) < DUP_RATIO:
                continue
            r = difflib.SequenceMatcher(None, seqs[a], seqs[c], autojunk=False).ratio()
            if r >= DUP_RATIO:
                dups.append({"a": [A[0] + 1, A[-1] + 1], "b": [C[0] + 1, C[-1] + 1],
                             "a_head": head(raw_lines, A[0], 50), "b_head": head(raw_lines, C[0], 50),
                             "tokens": [btok(A), btok(C)], "similarity": round(r, 3)})
    # keep only maximal pairs (drop pairs nested inside an already listed pair)
    dups.sort(key=lambda d: -(d["tokens"][0] + d["tokens"][1]))
    kept = []
    for d in dups:
        inside = any(k["a"][0] <= d["a"][0] and d["a"][1] <= k["a"][1] and
                     k["b"][0] <= d["b"][0] and d["b"][1] <= k["b"][1] for k in kept)
        if not inside:
            kept.append(d)
    # proof type from the share of tokens per block kind
    shares = {}
    for ob in out_blocks:
        if ob["role"] == "block":
            shares[ob["kind"]] = shares.get(ob["kind"], 0) + ob["tokens"]
    ptype = "mixed"
    for k in ("case", "calc", "have"):
        if shares.get(k, 0) >= TYPE_SHARE * total:
            ptype = k
    kind_share = {k: round(v / total * 100, 1) for k, v in shares.items()}
    # case-body candidates
    cases = []
    for i in body:
        s_ = lines[i].strip()
        if s_.startswith("case ") or s_.startswith("| "):
            sub = []
            for j in body:
                if j <= i:
                    continue
                if indent(lines[j]) > indent(lines[i]):
                    sub.append(j)
                else:
                    break
            tail = s_.split("=>", 1)[1] if "=>" in s_ else ""
            toks = line_tokens(tail) + [t for x in sub for t in line_tokens(lines[x])]
            cases.append((i, toks))
    case_dups = []
    for a in range(len(cases)):
        for c in range(a + 1, len(cases)):
            (ia, A), (ic, C) = cases[a], cases[c]
            if min(len(A), len(C)) < MIN_CASE or min(len(A), len(C)) / max(len(A), len(C)) < 0.8:
                continue
            r = difflib.SequenceMatcher(None, normalise(A), normalise(C), autojunk=False).ratio()
            if r >= CASE_RATIO:
                case_dups.append({"a": ia + 1, "b": ic + 1, "a_head": head(raw_lines, ia, 40),
                                  "b_head": head(raw_lines, ic, 40), "tokens": [len(A), len(C)],
                                  "similarity": round(r, 3)})
    return {
        "name": row["name"], "source": row.get("source", ""),
        "official": row["proof_length"], "counted": total,
        "check": "OK" if total == row["proof_length"] else "MISMATCH",
        "head_tokens": head_tokens, "wrapper_path": path,
        "type": ptype, "type_name": TYPE_NAMES[ptype], "kind_share": kind_share,
        "blocks": out_blocks, "repeat_candidates": kept, "case_candidates": case_dups,
    }


def to_md(results):
    L = ["# Warm-up 블록 분석", "",
         "proof token은 공식 `proof_length` 규칙. 각 문제의 블록 합 + `:= by` 줄 토큰 = 공식 값인지 확인함.",
         "src 줄은 benchmark JSONL `src` 필드 기준 줄 번호. 깊이 0은 증명 최상위, 1 이상은 감싸는 블록 안으로 내려가 나눈 블록.", "",
         "| # | 문제 | 출처 | 공식 | 확인 | 블록 수 | 가장 큰 블록 | 비중 | 반복 후보 | case 후보 |",
         "| ---: | --- | --- | ---: | --- | ---: | --- | ---: | ---: | ---: |"]
    for k, r in enumerate(results, 1):
        bl = [b for b in r["blocks"] if b["role"] == "block"]
        top = max(bl, key=lambda b: b["tokens"])
        L.append(f"| {r['idx']} | `{r['name'].split('.')[-1]}` | {r['source']} | {r['official']:,} | {r['check']} | "
                 f"{len(bl)} | `{top['head'][:38].replace('|','&#124;')}` (src {top['first_line']}–{top['last_line']}) | "
                 f"{top['share']}% | {len(r['repeat_candidates'])} | {len(r['case_candidates'])} |")
    L += ["", "## 유형별 묶음", "",
          f"블록 종류(`case` 분기, `calc` 단계, `have` 계열)별 토큰 비중이 {int(TYPE_SHARE*100)}% 이상인 종류로 유형을 정함.", "",
          "| 유형 | 문제 | 분할 규칙 |", "| --- | --- | --- |"]
    for t in ("case", "calc", "have", "mixed"):
        ids = [str(r["idx"]) for r in results if r["type"] == t]
        if ids:
            L.append(f"| {TYPE_NAMES[t]} | {', '.join(ids)} | {TYPE_RULES[t]} |")
    L += ["", "| # | 유형 | case | calc | have | 기타 |", "| ---: | --- | ---: | ---: | ---: | ---: |"]
    for r in results:
        ks = r["kind_share"]
        L.append(f"| {r['idx']} | {r['type_name']} | {ks.get('case', 0)}% | {ks.get('calc', 0)}% | {ks.get('have', 0)}% | {ks.get('other', 0)}% |")
    for r in results:
        L += ["", f"## {r['idx']}. `{r['name']}` ({r['source']}, {r['official']:,} 토큰, {r['check']}, {r['type_name']})", ""]
        if r["wrapper_path"]:
            L.append("감싸는 블록 안으로 내려가서 나눔: " + " → ".join(f"`{p}`" for p in r["wrapper_path"]))
            L.append("")
        L += ["| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |", "| --- | ---: | --- | --- | ---: | ---: |"]
        for b in r["blocks"]:
            h = b["head"].replace("|", "&#124;")
            L.append(f"| {b['first_line']}–{b['last_line']} | {b['depth']} | {b['role']} | `{h}` | {b['tokens']:,} | {b['share']}% |")
        for b in r["blocks"]:
            if b["children"]:
                L += ["", f"src {b['first_line']}–{b['last_line']} 블록({b['share']}%)을 한 단계 더 나눔:", "",
                      "| src 줄 | 종류 | 첫 줄 | 토큰 | 비중 |", "| --- | --- | --- | ---: | ---: |"]
                for c in b["children"]:
                    h = c["head"].replace("|", "&#124;")
                    L.append(f"| {c['first_line']}–{c['last_line']} | {c['kind']} | `{h}` | {c['tokens']:,} | {c['share']}% |")
        if r["repeat_candidates"]:
            L += ["", "반복 논증 후보 (이름을 정규화한 토큰열 유사도 ≥ 0.9, 후보일 뿐 동일성 증명 아님):", ""]
            for d in r["repeat_candidates"]:
                L.append(f"- src {d['a'][0]}–{d['a'][1]} `{d['a_head'].replace('|','&#124;')}` ({d['tokens'][0]}) ↔ "
                         f"src {d['b'][0]}–{d['b'][1]} `{d['b_head'].replace('|','&#124;')}` ({d['tokens'][1]}), 유사도 {d['similarity']}")
        if r["case_candidates"]:
            L += ["", "비슷한 case 본문 후보 (본문 토큰 ≥ 8, 유사도 ≥ 0.85):", ""]
            for d in r["case_candidates"]:
                L.append(f"- src {d['a']} `{d['a_head'].replace('|','&#124;')}` ({d['tokens'][0]}) ↔ "
                         f"src {d['b']} `{d['b_head'].replace('|','&#124;')}` ({d['tokens'][1]}), 유사도 {d['similarity']}")
    return "\n".join(L) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("jsonl")
    ap.add_argument("--rows", nargs="*", type=int)
    ap.add_argument("--json")
    ap.add_argument("--md")
    a = ap.parse_args()
    rows = [json.loads(l) for l in open(a.jsonl, encoding="utf-8") if l.strip()]
    sel = a.rows or list(range(1, len(rows) + 1))
    res = []
    for k in sel:
        r = analyse(rows[k - 1]); r["idx"] = k; res.append(r)
        bl = [b for b in r["blocks"] if b["role"] == "block"]
        print(f"{k:2d} {r['check']:8s} official={r['official']:5d} counted={r['counted']:5d} "
              f"blocks={len(bl):2d} repeats={len(r['repeat_candidates'])} cases={len(r['case_candidates'])} {r['name']}")
    if a.json:
        json.dump(res, open(a.json, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    if a.md:
        open(a.md, "w", encoding="utf-8").write(to_md(res))
    return 0 if all(r["check"] == "OK" for r in res) else 1


if __name__ == "__main__":
    sys.exit(main())
