#!/usr/bin/env python3
"""Remove `have` blocks that Lean reports as unused, until none is reported.

Rule (no LLM involved; the same input always gives the same output)
  1. Compile the declaration with
     `set_option linter.unusedVariables.analyzeTactics true`.
  2. For every "unused variable `x`" warning whose line starts a `have`,
     `obtain`, `let` or `set` (optionally after `·`), delete that line and the
     more-indented lines below it (its proof).
  3. Compile again. If it compiles without errors, keep the removal and go
     back to 1. If not, try the reported blocks one at a time and keep only
     those that compile.
  4. Stop when no `have`-line warning is left, or after MAX_PASSES passes.
The tunable parts are collected in the "규칙 설정" block below.

Every kept state compiles, is checked with `#print axioms`, and its proof
tokens are counted with the official `proof_length` rule (proof_tokens.py).

usage (from this folder):
  # standalone mode: the benchmark row's own header (`import Mathlib`) + the declaration,
  # compiled in a lake project pinned to the row's Lean/Mathlib version
  python prune_unused.py --jsonl benchmark_data_warmup.jsonl --row 14 \
      --project project --out results/prune14
  # --header FILE replaces the benchmark header (used only for quick local checks).

  # file mode: the declaration is replaced inside row["file_path"] lines
  # start_line..end_line of the checked-out repository (version_info commit, built),
  # so the original file context (namespaces, variables, earlier lemmas) is kept.
  # Compiled with `lake lean` so the library's own options apply; the file is
  # restored byte for byte afterwards.
  python prune_unused.py --jsonl benchmark_data_warmup.jsonl --row 10 \
      --repo <ArkLib checkout> --out results/prune10
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "local-v4.26", "tools"))
from proof_tokens import proof_length  # noqa: E402

# =====================================================================
# 규칙 설정: 여기만 바꾸면 규칙이 바뀐다 (박채원 검토·수정 구간)
# =====================================================================

# [규칙 1] 반복 횟수 상한. 지운 뒤 새로 안 쓰이게 된 have를 다시 찾기 위해 반복한다.
MAX_PASSES = 10

# [규칙 2] 지울 수 있는 블록의 첫 단어. 린터 경고가 이 단어로 시작하는 줄에 나올 때만 지운다.
#   예: ("have",)만 두면 obtain/let/set으로 만든 변수는 건드리지 않는다.
REMOVABLE_KEYWORDS = ("have", "obtain", "let", "set")

# [규칙 3] `· have …`처럼 bullet 뒤의 블록도 지울지.
ALLOW_BULLET = True

# [규칙 4] 한꺼번에 지웠더니 컴파일 에러가 나면, 하나씩 지워 보며 통과하는 것만 남길지.
#   False면 그 회차에서 멈춘다.
FALLBACK_ONE_BY_ONE = True

# [규칙 5] 허용 공리. 지운 결과의 `#print axioms`가 이 안에 있어야 받아들인다.
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def accept(prev: dict, new: dict) -> bool:
    """[규칙 6] 새 상태를 받아들일 조건. prev/new는 check()의 결과."""
    if new["errors"] > 0:                       # 컴파일 에러가 없어야 함
        return False
    if new["axioms"] is None:                   # #print axioms 결과가 있어야 함
        return False
    axioms = {a.strip() for a in new["axioms"].split(",") if a.strip()}
    # 허용 공리 + 원본 증명이 이미 쓰던 공리만 (원본에 없던 sorryAx 등은 차단)
    if not axioms <= ALLOWED_AXIOMS | BASE_AXIOMS:
        return False
    if new["tokens"] > prev["tokens"]:          # proof token이 늘면 안 됨
        return False
    return True

# =====================================================================
# 아래는 실행 부분 (규칙을 바꿀 때는 보통 손대지 않아도 됨)
# =====================================================================

_bullet = r"(·\s*)?" if ALLOW_BULLET else ""
HAVE_START = re.compile(r"^\s*" + _bullet + r"(" + "|".join(REMOVABLE_KEYWORDS) + r")\b")
WARN = re.compile(r":(\d+):(\d+): warning: unused variable `([^`]+)`")
# Lean 형식 `file:l:c: error`와 Lake 형식 `error: …` 둘 다 센다
ERR = re.compile(r":\d+:\d+: error|^error:", re.M)
# 공리 목록은 길면 여러 줄로 나뉘어 출력된다
AX = re.compile(r"depends on axioms: \[(.*?)\]", re.S)
BASE_AXIOMS: set = set()   # 원본 증명의 공리 (pass0에서 채움)


def indent(s: str) -> int:
    return len(s) - len(s.lstrip(" "))


def build_file(header: str, decl: str, name: str) -> tuple[str, int]:
    pre = header.rstrip("\n") + "\n\nset_option linter.unusedVariables.analyzeTactics true\n\n"
    text = pre + decl.rstrip("\n") + f"\n\n#print axioms {name}\n"
    return text, pre.count("\n")          # offset: lines before the declaration


def compile_lean(project: str, path: str, timeout: int, rel: str | None = None) -> str:
    # file mode: `lake lean` applies the library's own options (leanOptions / moreLeanArgs)
    cmd = ["lake", "lean", rel] if rel else ["lake", "env", "lean", path]
    r = subprocess.run(cmd, cwd=project, capture_output=True,
                       text=True, encoding="utf-8", errors="replace", timeout=timeout)
    return r.stdout + r.stderr


def block_lines(lines: list[str], i: int) -> list[int]:
    out, j = [i], i + 1
    while j < len(lines) and (not lines[j].strip() or indent(lines[j]) > indent(lines[i])):
        out.append(j)
        j += 1
    while out and not lines[out[-1]].strip():   # keep trailing blank lines
        out.pop()
    return out


def build_in_file(ctx, decl: str, name: str) -> tuple[str, int]:
    head, doc, after = ctx
    # option set above the doc comment (an `in` between a doc comment and the declaration does not parse)
    pre = head + "set_option linter.unusedVariables.analyzeTactics true\n" + doc
    text = pre + decl.rstrip("\n") + f"\n\n#print axioms {name}\n" + after
    return text, pre.count("\n")


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


def check(project, workdir, tag, header, decl, row, timeout, ctx=None):
    if ctx is None:
        text, off = build_file(header, decl, row["name"])
        path = os.path.abspath(os.path.join(workdir, f"{tag}.lean"))
        open(path, "w", encoding="utf-8").write(text)
    else:
        text, off = build_in_file(ctx["parts"], decl, row["name"])
        path = ctx["path"]
        open(path, "w", encoding="utf-8", newline="\n").write(text)
        open(os.path.join(workdir, f"{tag}.lean"), "w", encoding="utf-8", newline="\n").write(text)
    log = compile_lean(project, path, timeout, ctx["rel"] if ctx else None)
    open(os.path.join(workdir, f"{tag}.log"), "w", encoding="utf-8").write(log)
    errors = len(ERR.findall(log))
    ax = AX.search(log)
    unused = []
    dl = decl.split("\n")
    for m in WARN.finditer(log):
        k = int(m.group(1)) - 1 - off             # 0-based line inside decl
        if 0 <= k < len(dl) and HAVE_START.match(dl[k]):
            unused.append((k, m.group(3)))
    return {"errors": errors, "axioms": " ".join(ax.group(1).split()) if ax else None,
            "tokens": proof_length(decl, row["statement"]), "unused": sorted(set(unused))}


def remove(decl: str, starts: list[int]) -> str:
    lines = decl.split("\n")
    drop = set()
    for k in starts:
        drop.update(block_lines(lines, k))
    return "\n".join(x for i, x in enumerate(lines) if i not in drop)


def run(row, project, header, workdir, timeout, ctx=None):
    os.makedirs(workdir, exist_ok=True)
    decl = row["src"]
    passes = []
    def chk(tag, d):
        return check(project, workdir, tag, header, d, row, timeout, ctx)
    st = chk("pass0", decl)
    if st["errors"] or st["axioms"] is None:
        raise SystemExit(f"reference does not compile in this environment (see {workdir}/pass0.log)")
    BASE_AXIOMS.update(a.strip() for a in st["axioms"].split(",") if a.strip())
    base_tokens = st["tokens"]
    passes.append({"pass": 0, "tokens": st["tokens"], "errors": 0, "axioms": st["axioms"], "removed": []})
    for p in range(1, MAX_PASSES + 1):
        if not st["unused"]:
            break
        cand = remove(decl, [k for k, _ in st["unused"]])
        nst = chk(f"pass{p}", cand)
        removed = [n for _, n in st["unused"]]
        if not accept(st, nst):
            if not FALLBACK_ONE_BY_ONE:
                break
            # keep only the removals that are accepted on their own, one at a time
            kept, cur, cur_st = [], decl, st
            for k, n in sorted(st["unused"], reverse=True):     # bottom-up keeps line numbers valid
                trial = remove(cur, [k])
                tst = chk(f"pass{p}_{n}", trial)
                if accept(cur_st, tst):
                    cur, cur_st = trial, tst
                    kept.append(n)
            if not kept:
                break
            cand, nst, removed = cur, cur_st, kept
        decl, st = cand, nst
        passes.append({"pass": p, "tokens": st["tokens"], "errors": st["errors"],
                       "axioms": st["axioms"], "removed": removed})
    open(os.path.join(workdir, "final.lean"), "w", encoding="utf-8").write(decl + "\n")
    return {"row": row["name"], "official_tokens": row["proof_length"], "start_tokens": base_tokens,
            "final_tokens": st["tokens"],
            "reduction_pct": round((base_tokens - st["tokens"]) / base_tokens * 100, 3),
            "passes": passes}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jsonl", required=True)
    ap.add_argument("--row", type=int, required=True)
    ap.add_argument("--project", help="lake project for standalone mode")
    ap.add_argument("--repo", help="checked-out repository for file mode")
    ap.add_argument("--header")
    ap.add_argument("--out", required=True)
    ap.add_argument("--timeout", type=int, default=1800)
    a = ap.parse_args()
    rows = [json.loads(l) for l in open(a.jsonl, encoding="utf-8") if l.strip()]
    row = rows[a.row - 1]
    ctx = None
    if a.repo:
        path = os.path.abspath(os.path.join(a.repo, row["file_path"]))
        orig = open(path, "rb").read()
        lines = orig.decode("utf-8").replace("\r\n", "\n").split("\n")
        s0, e0 = locate_decl(lines, row)
        h0 = decl_head_start(lines, s0)
        ctx = {"path": path, "rel": row["file_path"], "parts": ("".join(l + "\n" for l in lines[:h0]),
                                       "".join(l + "\n" for l in lines[h0:s0]),
                                       "\n" + "\n".join(lines[e0:]))}
        project, header = a.repo, ""
    else:
        if not a.project:
            raise SystemExit("give --project (standalone) or --repo (file mode)")
        project = a.project
        header = open(a.header, encoding="utf-8").read() if a.header else row["header"]
    try:
        res = run(row, project, header, a.out, a.timeout, ctx)
    finally:
        if ctx:
            open(ctx["path"], "wb").write(orig)   # restore the repository file byte for byte
    res["row_index"] = a.row
    res["header"] = ("file mode: " + row["file_path"]) if a.repo else (
        "custom: " + os.path.basename(a.header) if a.header else "benchmark header")
    json.dump(res, open(os.path.join(a.out, "result.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print(json.dumps({k: res[k] for k in ("row", "start_tokens", "final_tokens", "reduction_pct")}, ensure_ascii=False))
    for p in res["passes"]:
        print(f"  pass {p['pass']}: tokens {p['tokens']} errors {p['errors']} axioms [{p['axioms']}] removed {p['removed']}")


if __name__ == "__main__":
    main()
