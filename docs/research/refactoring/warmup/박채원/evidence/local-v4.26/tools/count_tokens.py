#!/usr/bin/env python3
"""Official proof_length for measurement files that carry a header and #print axioms.
usage: count_tokens.py <statement.lean> <file.lean> [...]"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from proof_tokens import proof_length
stmt = open(sys.argv[1], encoding='utf-8').read().rstrip('\n')
for p in sys.argv[2:]:
    t = open(p, encoding='utf-8').read()
    t = t[t.index('theorem'):].split('#print axioms')[0]
    print(f"{proof_length(t, stmt):6d} {p}")
