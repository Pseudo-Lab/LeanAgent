#!/usr/bin/env python3
"""Summarise per-problem proof-token reductions and their confidence interval.

Each problem contributes one reduction rate r_i = (start - final) / start.
Lean compilation and proof_length are deterministic, so there is no
measurement noise within a problem; the uncertainty reported here is the
variation between problems, i.e. "if the same rule is applied to a new
problem of the same type, what mean reduction should we expect".

Two intervals are reported for the mean of r_i:
  - percentile bootstrap over problems (B resamples, fixed seed)
  - Student t interval
With few problems both are wide and the bootstrap has few distinct
resamples; read them together with n.

usage:
  python reduction_ci.py out13/result.json out14/result.json out15/result.json --md ci.md
"""
from __future__ import annotations

import argparse
import json
import math
import random
import statistics

B = 20000
SEED = 20261022
LEVEL = 0.95
T975 = {1: 12.706, 2: 4.303, 3: 3.182, 4: 2.776, 5: 2.571, 6: 2.447, 7: 2.365, 8: 2.306,
        9: 2.262, 10: 2.228, 11: 2.201, 12: 2.179, 13: 2.160, 14: 2.145, 15: 2.131,
        20: 2.086, 30: 2.042}


def t_quantile(df: int) -> float:
    if df in T975:
        return T975[df]
    keys = sorted(T975)
    for a, b in zip(keys, keys[1:]):
        if a < df < b:
            return T975[a] + (T975[b] - T975[a]) * (df - a) / (b - a)
    return 1.96


def summarise(rates: list[float]) -> dict:
    n = len(rates)
    mean = statistics.fmean(rates)
    out = {"n": n, "mean": mean, "min": min(rates), "max": max(rates)}
    if n >= 2:
        sd = statistics.stdev(rates)
        h = t_quantile(n - 1) * sd / math.sqrt(n)
        out.update({"sd": sd, "t_low": mean - h, "t_high": mean + h})
        rng = random.Random(SEED)
        boots = sorted(statistics.fmean(rng.choices(rates, k=n)) for _ in range(B))
        out.update({"boot_low": boots[int((1 - LEVEL) / 2 * B)],
                    "boot_high": boots[int((1 + LEVEL) / 2 * B) - 1],
                    "distinct_resamples": math.comb(2 * n - 1, n)})
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("results", nargs="+")
    ap.add_argument("--md")
    ap.add_argument("--json")
    a = ap.parse_args()
    rows = [json.load(open(p, encoding="utf-8")) for p in a.results]
    rows.sort(key=lambda r: r.get("row_index", 0))
    rates = [(r["start_tokens"] - r["final_tokens"]) / r["start_tokens"] for r in rows]
    s = summarise(rates)
    pct = lambda x: f"{x * 100:.2f}%"
    L = ["| # | 정리 | 시작 토큰 | 최종 토큰 | 감소 | 감소율 | 적용한 변경 수 | 헤더 |",
         "| ---: | --- | ---: | ---: | ---: | ---: | ---: | --- |"]
    for r, x in zip(rows, rates):
        nrem = sum(len(p["removed"]) for p in r["passes"]) if "passes" in r else len(r.get("chosen", []))
        L.append(f"| {r.get('row_index', '')} | `{r['row']}` | {r['start_tokens']:,} | {r['final_tokens']:,} | "
                 f"{r['start_tokens'] - r['final_tokens']:,} | {pct(x)} | {nrem} | {r.get('header', '')} |")
    L += ["", f"- 문제 수 n = {s['n']}, 평균 감소율 {pct(s['mean'])}, 범위 {pct(s['min'])}–{pct(s['max'])}"]
    if s["n"] >= 2:
        L += [f"- 95% t 구간: {pct(s['t_low'])} – {pct(s['t_high'])} (표준편차 {pct(s['sd'])})",
              f"- 95% 부트스트랩 백분위 구간: {pct(s['boot_low'])} – {pct(s['boot_high'])} "
              f"(B = {B:,}, 서로 다른 재표본 수 {s['distinct_resamples']})"]
    text = "\n".join(L) + "\n"
    print(text)
    if a.md:
        open(a.md, "w", encoding="utf-8").write(text)
    if a.json:
        json.dump({"rates": rates, "summary": s}, open(a.json, "w", encoding="utf-8"), indent=1)


if __name__ == "__main__":
    main()
