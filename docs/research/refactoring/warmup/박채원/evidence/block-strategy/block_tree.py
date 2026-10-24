#!/usr/bin/env python3
"""Block tree, duplicate groups and alignment for Lean `by` proofs (text only).

Rules (designed with 박채원; no LLM; the same input always gives the same output)
  1. Stack: read the proof line by line and build a tree from indentation.
     A line's parent is the closest previous line with smaller indentation.
     A node = one line + all its descendants (that line's sub-proof).
  2. DFS (post-order): subtree tokens = own line tokens + children's subtree
     tokens. Tokens follow the official proof_length (proof_tokens.py), so the
     root total plus the `:= by` line equals the official value; this is checked.
  3. Hash: every subtree with at least MIN_GROUP tokens is alpha-normalised
     (local names -> v0, v1, ... in order of appearance) and hashed. Subtrees
     with the same hash are "same up to renaming". Only maximal groups are kept
     (a group whose members all lie inside members of another group is dropped).
  4. Alignment DP: subtrees of the have family (have/obtain/let/set/suffices)
     with at least MIN_ALIGN tokens and size ratio >= SIZE_RATIO are aligned
     token by token with edit-distance DP on normalised tokens. Pairs with
     similarity >= ALIGN_RATIO and not already in an exact group are reported,
     together with the raw tokens that differ at aligned positions (candidate
     function arguments).

usage:
  python block_tree.py benchmark_data_warmup.jsonl --rows 4 10 11 12 13 14 15 \
      --md tree.md --json tree.json
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "block-analyzer"))
sys.path.insert(0, os.path.join(HERE, "..", "local-v4.26", "tools"))
from block_analyzer import (strip_comments_keep_lines, line_tokens, indent,  # noqa: E402
                            normalise, head, remove_comments)

# ===================== 규칙 설정 =====================
MIN_GROUP = 20      # [규칙 3] 해시 그룹에 넣을 최소 서브트리 토큰
MIN_ALIGN = 40      # [규칙 4] 정렬할 최소 서브트리 토큰
SIZE_RATIO = 0.8    # [규칙 4] 두 블록 크기 비율 하한 (작은 쪽 / 큰 쪽)
ALIGN_RATIO = 0.85  # [규칙 4] 정렬 유사도 하한 = 1 - 편집거리 / 긴 쪽 길이
HAVE_FAMILY = ("have", "obtain", "let", "set", "suffices", "·")
TOP_N = 8           # 보고서에 보일 큰 노드 수
# ====================================================


class Node:
    __slots__ = ("line", "ind", "own", "children", "parent", "sub", "lines", "toks")

    def __init__(self, line, ind, own):
        self.line, self.ind, self.own = line, ind, own
        self.children, self.parent, self.sub, self.lines, self.toks = [], None, 0, [], []


def build_tree(lines, body):
    """Rule 1: stack over indentation."""
    root = Node(-1, -1, [])
    stack = [root]
    for i in body:
        n = Node(i, indent(lines[i]), line_tokens(lines[i]))
        while stack[-1].ind >= n.ind:
            stack.pop()
        n.parent = stack[-1]
        stack[-1].children.append(n)
        stack.append(n)
    return root


def dfs(n):
    """Rule 2: post-order subtree tokens and line lists."""
    toks, lines = list(n.own), ([n.line] if n.line >= 0 else [])
    for c in n.children:
        dfs(c)
        toks += c.toks
        lines += c.lines
    n.toks, n.lines, n.sub = toks, lines, len(toks)


def walk(n):
    yield n
    for c in n.children:
        yield from walk(c)


def edit_align(a, b):
    """Rule 4: Levenshtein DP with back-pointers; returns distance and aligned pairs."""
    n, m = len(a), len(b)
    D = [[0] * (m + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        D[i][0] = i
    for j in range(m + 1):
        D[0][j] = j
    for i in range(1, n + 1):
        ai, Di, Dp = a[i - 1], D[i], D[i - 1]
        for j in range(1, m + 1):
            Di[j] = min(Dp[j] + 1, Di[j - 1] + 1, Dp[j - 1] + (ai != b[j - 1]))
    pairs, i, j = [], n, m
    while i > 0 and j > 0:
        if D[i][j] == D[i - 1][j - 1] + (a[i - 1] != b[j - 1]):
            pairs.append((i - 1, j - 1)); i -= 1; j -= 1
        elif D[i][j] == D[i - 1][j] + 1:
            i -= 1
        else:
            j -= 1
    return D[n][m], pairs[::-1]


def kind(lines, n):
    w = lines[n.line].split()
    return w[0] if w else ""


def analyse(row):
    src, stmt = row["src"], row["statement"]
    text = strip_comments_keep_lines(src)
    pos = text.index(":=", len(strip_comments_keep_lines(stmt))) + 2
    first = text.count("\n", 0, pos)
    lines, raw = text.split("\n"), src.split("\n")
    head_tokens = len(line_tokens(text[pos:].split("\n", 1)[0]))
    body = [i for i in range(first + 1, len(lines)) if lines[i].strip()]
    root = build_tree(lines, body)
    dfs(root)
    total = head_tokens + root.sub
    nodes = [n for n in walk(root) if n.line >= 0]

    # Rule 3: hash groups of identical normalised subtrees
    buckets = {}
    for n in nodes:
        if n.sub >= MIN_GROUP:
            h = hashlib.sha1(" ".join(normalise(n.toks)).encode()).hexdigest()
            buckets.setdefault(h, []).append(n)
    groups = []
    for h, g in buckets.items():
        mem, used = [], set()
        for n in sorted(g, key=lambda x: x.line):
            if used & set(n.lines):
                continue
            mem.append(n); used |= set(n.lines)
        if len(mem) >= 2:
            groups.append(mem)
    groups.sort(key=lambda g: -(len(g) - 1) * g[0].sub)
    kept = []
    for g in groups:
        inside = any(all(any(set(n.lines) <= set(k.lines) for k in big) for n in g) for big in kept)
        if not inside:
            kept.append(g)
    def owner(n):
        """(group index, member index) of the exact-group member that contains n, if any."""
        for gi, g in enumerate(kept):
            for mi, mnode in enumerate(g):
                if set(n.lines) <= set(mnode.lines):
                    return gi, mi
        return None

    # Rule 4: alignment DP among have-family subtrees
    cand = [n for n in nodes if n.sub >= MIN_ALIGN and kind(lines, n) in HAVE_FAMILY]
    aligned = []
    for x in range(len(cand)):
        for y in range(x + 1, len(cand)):
            A, B = cand[x], cand[y]
            if set(A.lines) & set(B.lines):
                continue
            oa, ob = owner(A), owner(B)
            if oa and ob and oa[0] == ob[0] and oa[1] != ob[1]:
                continue  # already explained by an exact group
            if min(A.sub, B.sub) / max(A.sub, B.sub) < SIZE_RATIO:
                continue
            na, nb = normalise(A.toks), normalise(B.toks)
            dist, pairs = edit_align(na, nb)
            sim = 1 - dist / max(len(na), len(nb))
            if sim < ALIGN_RATIO:
                continue
            diffs = Counter((A.toks[i], B.toks[j]) for i, j in pairs if A.toks[i] != B.toks[j])
            aligned.append({"a": [A.line + 1, A.lines[-1] + 1], "b": [B.line + 1, B.lines[-1] + 1],
                            "a_head": head(raw, A.line, 60), "b_head": head(raw, B.line, 60),
                            "tokens": [A.sub, B.sub], "edit_distance": dist, "similarity": round(sim, 3),
                            "raw_differences": [[p, q, c] for (p, q), c in diffs.most_common(8)],
                            "unaligned_tokens": len(A.toks) + len(B.toks) - 2 * len(pairs)})
    # keep maximal aligned pairs
    aligned.sort(key=lambda d: -(d["tokens"][0] + d["tokens"][1]))
    keep = []
    for d in aligned:
        if not any(k["a"][0] <= d["a"][0] and d["a"][1] <= k["a"][1] and
                   k["b"][0] <= d["b"][0] and d["b"][1] <= k["b"][1] for k in keep):
            keep.append(d)

    top = sorted(nodes, key=lambda n: -n.sub)[:TOP_N]
    return {
        "name": row["name"], "official": row["proof_length"], "counted": total,
        "check": "OK" if total == row["proof_length"] else "MISMATCH",
        "nodes": len(nodes),
        "largest": [{"line": n.line + 1, "last": n.lines[-1] + 1, "depth": depth(n),
                     "head": head(raw, n.line, 60), "tokens": n.sub,
                     "share": round(n.sub / total * 100, 1)} for n in top],
        "exact_groups": [{"members": [[n.line + 1, n.lines[-1] + 1] for n in g],
                          "heads": [head(raw, n.line, 50) for n in g], "tokens_each": g[0].sub,
                          "count": len(g), "repeat_tokens": (len(g) - 1) * g[0].sub} for g in kept],
        "near_pairs": keep,
    }


def depth(n):
    d = 0
    while n.parent is not None and n.parent.line >= 0:
        d += 1; n = n.parent
    return d


def esc(s):
    return s.replace("|", "&#124;")


def to_md(res):
    L = ["# 중간 명제형 블록 트리 분석", "",
         "토큰은 공식 `proof_length` 규칙. 확인 = 루트 서브트리 토큰 + `:= by` 줄 토큰이 공식 값과 같은지.", "",
         "| # | 정리 | 공식 | 확인 | 노드 수 | 확정 중복 그룹 | 반복 토큰 합 | 근사 중복 쌍 |",
         "| ---: | --- | ---: | --- | ---: | ---: | ---: | ---: |"]
    for r in res:
        L.append(f"| {r['idx']} | `{r['name'].split('.')[-1]}` | {r['official']:,} | {r['check']} | {r['nodes']} | "
                 f"{len(r['exact_groups'])} | {sum(g['repeat_tokens'] for g in r['exact_groups']):,} | {len(r['near_pairs'])} |")
    L += ["", "반복 토큰 = (개수 − 1) × 블록 토큰. 같은 증명을 한 번만 쓰면 없어지는 토큰이며, 보조정리 호출 비용은 빼지 않은 값이다."]
    for r in res:
        L += ["", f"## {r['idx']}. `{r['name']}` ({r['official']:,} 토큰, {r['check']})", "",
              "큰 노드 (서브트리 토큰 순)", "", "| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |", "| --- | ---: | --- | ---: | ---: |"]
        for n in r["largest"]:
            L.append(f"| {n['line']}–{n['last']} | {n['depth']} | `{esc(n['head'])}` | {n['tokens']:,} | {n['share']}% |")
        if r["exact_groups"]:
            L += ["", "확정 중복 그룹 (이름 정규화 후 해시 일치)", "", "| 개수 | 블록 토큰 | 반복 토큰 | 위치와 첫 줄 |", "| ---: | ---: | ---: | --- |"]
            for g in r["exact_groups"]:
                where = "<br>".join(f"src {a}–{b} `{esc(h)}`" for (a, b), h in zip(g["members"], g["heads"]))
                L.append(f"| {g['count']} | {g['tokens_each']} | {g['repeat_tokens']} | {where} |")
        if r["near_pairs"]:
            L += ["", "근사 중복 쌍 (편집 거리 DP 정렬)", "", "| 블록 A | 블록 B | 토큰 | 유사도 | 다른 토큰 (A → B, 횟수) |", "| --- | --- | --- | ---: | --- |"]
            for d in r["near_pairs"]:
                diff = ", ".join(f"`{esc(p)}`→`{esc(q)}` {c}" for p, q, c in d["raw_differences"])
                L.append(f"| src {d['a'][0]}–{d['a'][1]} `{esc(d['a_head'][:40])}` | src {d['b'][0]}–{d['b'][1]} `{esc(d['b_head'][:40])}` | "
                         f"{d['tokens'][0]}·{d['tokens'][1]} | {d['similarity']} | {diff} |")
    return "\n".join(L) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("jsonl")
    ap.add_argument("--rows", nargs="*", type=int)
    ap.add_argument("--md")
    ap.add_argument("--json")
    a = ap.parse_args()
    rows = [json.loads(l) for l in open(a.jsonl, encoding="utf-8") if l.strip()]
    res = []
    for k in (a.rows or range(1, len(rows) + 1)):
        r = analyse(rows[k - 1]); r["idx"] = k; res.append(r)
        print(f"{k:2d} {r['check']} nodes={r['nodes']} exact_groups={len(r['exact_groups'])} "
              f"near_pairs={len(r['near_pairs'])} {r['name']}")
    if a.md:
        open(a.md, "w", encoding="utf-8").write(to_md(res))
    if a.json:
        json.dump(res, open(a.json, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    return 0 if all(r["check"] == "OK" for r in res) else 1


if __name__ == "__main__":
    sys.exit(main())
