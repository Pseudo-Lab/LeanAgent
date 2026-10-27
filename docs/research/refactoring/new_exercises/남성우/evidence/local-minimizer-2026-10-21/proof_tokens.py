#!/usr/bin/env python3
"""Proof-length (token) counter for Lean Refactor Arena problems.

Re-implements the `proof_length` listing in Appendix J of the Lean Refactor
paper (arXiv:2605.20244v2). Two helpers used by that listing are not printed in
the paper (`remove_comments`, `return_theorem_to_prove`); they are reconstructed
here. The paper's HTML renders one operator as "-1"; the value that reproduces
the official numbers is the superscript inverse "⁻¹". The operator list matches
`proof_length` in the authors' public repository (delta-lab-ai/lean-refactor,
lean_refactor/utils.py), where the arrow entry is "←", so ASCII "<-" counts as
two tokens.

Self-check: `python3 proof_tokens.py --check benchmark_data_warmup.jsonl`
reproduces the official `proof_length` of all 15 warm-up rows (checked on
2026-10-11). Counts for new candidates are therefore expected to match the
Arena worker, but only an official submission can confirm that.

usage:
  proof_tokens.py --check <benchmark.jsonl>
  proof_tokens.py --statement <statement.lean> <declaration.lean> [...]
"""
from __future__ import annotations

import argparse
import json
import sys

OPERATORS = [
    ":=", "!=", "&&", "-.", "->", "←", "..", "...", "::", ":>",
    "<;>", ";;", "==", "||", "=>", "<=", ">=", "⁻¹", "?_",
]
_SPACED = [" ".join(op) for op in OPERATORS]
_TABLE = dict(zip(_SPACED, OPERATORS))
_WORD_CHARS = "._'"


def remove_comments(src: str) -> str:
    """Drop `/- -/` block comments (nested), `--` line comments and blank lines."""
    out: list[str] = []
    i, n, depth, in_str = 0, len(src), 0, False
    while i < n:
        two = src[i:i + 2]
        if depth:
            if two == "/-":
                depth, i = depth + 1, i + 2
            elif two == "-/":
                depth, i = depth - 1, i + 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
        elif in_str:
            out.append(src[i])
            if src[i] == "\\" and i + 1 < n:
                out.append(src[i + 1])
                i += 1
            elif src[i] == '"':
                in_str = False
            i += 1
        elif two == "/-":
            depth, i = 1, i + 2
        elif two == "--":
            while i < n and src[i] != "\n":
                i += 1
        else:
            in_str = src[i] == '"'
            out.append(src[i])
            i += 1
    return "\n".join(line for line in "".join(out).splitlines() if line.strip())


def lex(snippet: str) -> str:
    lines = []
    for line in snippet.splitlines():
        tokens: list[str] = []
        token = ""
        for ch in line:
            if ch == " ":
                if token:
                    tokens.append(token)
                    token = ""
            elif ch.isalnum() or ch in _WORD_CHARS:
                token += ch
            else:
                if token:
                    tokens.append(token)
                    token = ""
                tokens.append(ch)
        if token:
            tokens.append(token)
        joined = " ".join(tokens)
        for spaced in _SPACED:
            if spaced in joined:
                joined = joined.replace(spaced, _TABLE[spaced])
        lines.append(joined)
    return "\n".join(lines)


def proof_body(declaration: str, statement: str) -> str:
    """Text after the `:=` that follows the (unchanged) statement."""
    decl = remove_comments(declaration)
    stmt = remove_comments(statement)
    if not decl.startswith(stmt):
        raise ValueError("declaration does not start with the benchmark statement")
    return decl[decl.index(":=", len(stmt)) + 2:]


def proof_length(declaration: str, statement: str) -> int:
    lexed = lex(proof_body(declaration, statement))
    return sum(len(line.split(" ")) for line in lexed.splitlines())


def _check(path: str) -> int:
    rows = [json.loads(l) for l in open(path, encoding="utf-8") if l.strip()]
    bad = 0
    for i, row in enumerate(rows, 1):
        got = proof_length(row["src"], row["statement"])
        ok = got == row["proof_length"]
        bad += not ok
        print(f"{i:2d} {'ok ' if ok else 'DIFF'} official={row['proof_length']:5d} "
              f"local={got:5d} {row['name']}")
    print(f"{len(rows) - bad}/{len(rows)} rows reproduce the official proof_length")
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", metavar="JSONL")
    ap.add_argument("--statement", metavar="FILE")
    ap.add_argument("declarations", nargs="*")
    args = ap.parse_args()
    if args.check:
        return _check(args.check)
    if not args.statement or not args.declarations:
        ap.error("give --check JSONL, or --statement FILE and declaration files")
    statement = open(args.statement, encoding="utf-8").read().rstrip("\n")
    for path in args.declarations:
        decl = open(path, encoding="utf-8").read()
        print(f"{proof_length(decl, statement):6d} {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
