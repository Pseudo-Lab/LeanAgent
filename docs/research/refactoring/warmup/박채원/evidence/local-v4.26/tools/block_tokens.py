#!/usr/bin/env python3
"""Official proof_length split by line ranges of the measured files.

proof_length counts tokens line by line, so per-range counts add up to the
total (plus the `by` that ends the statement line).
usage (from evidence/local-v4.26/):  python tools/block_tokens.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from proof_tokens import lex, proof_length, remove_comments  # noqa: E402

BASE = os.path.dirname(HERE)

BLOCKS = {
    ("P14_ref.lean", "statement14.lean"): [
        ("h_no_empty", 16, 21),
        ("h_subset_or_compl: header + h3 (A)", 23, 64),
        ("h_subset_or_compl: h4 (A complement)", 66, 101),
        ("h_subset_or_compl: rest", 103, 135),
        ("h_not_both", 137, 147),
        ("h_card: Q, card_bij' (h1)", 149, 220),
        ("h_card: union/disjoint (h2)", 222, 267),
        ("h_card: arithmetic (h3-h5)", 269, 301),
        ("exact h_card", 303, 303),
    ],
    ("P15_ref.lean", "statement15.lean"): [
        ("h_main, h1-h4", 16, 25),
        ("h5 (d, e)", 27, 74),
        ("h6 (e, f)", 76, 123),
        ("h7", 125, 198),
        ("h8", 200, 231),
        ("h9", 233, 286),
        ("end", 288, 291),
    ],
    ("P14_mine.lean", "statement14.lean"): [
        ("classical + key", 16, 49),
        ("hdisj, hunion", 50, 62),
        ("hcard", 63, 68),
        ("final arithmetic", 69, 74),
    ],
    ("P15_mine.lean", "statement15.lean"): [
        ("intro, obtain, subst", 16, 20),
        ("key + simp only [key]", 21, 27),
        ("hS", 28, 31),
        ("h3", 32, 35),
        ("final", 36, 37),
    ],
}


def count(lines):
    text = remove_comments("\n".join(lines))
    if not text.strip():
        return 0
    return sum(len(line.split(" ")) for line in lex(text).splitlines())


def main():
    for (name, stmt_name), blocks in BLOCKS.items():
        src = open(os.path.join(BASE, name), encoding="utf-8").read()
        stmt = open(os.path.join(HERE, stmt_name), encoding="utf-8").read().rstrip("\n")
        decl = src[src.index("theorem"):].split("#print axioms")[0]
        total = proof_length(decl, stmt)
        lines = src.split("\n")
        print(f"{name}: proof_length {total}")
        acc = 1  # the `by` at the end of the statement line
        for label, a, b in blocks:
            c = count(lines[a - 1:b])
            acc += c
            print(f"  L{a}-{b:<4} {c:5d} {100 * c / total:5.1f}%  {label}")
        print(f"  sum of blocks + 1 (`by`) = {acc}  {'OK' if acc == total else 'MISMATCH'}")


if __name__ == "__main__":
    main()
