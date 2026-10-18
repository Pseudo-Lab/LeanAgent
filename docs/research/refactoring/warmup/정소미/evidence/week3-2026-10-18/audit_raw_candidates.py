#!/usr/bin/env python3
"""Audit all 45 frozen PR #19 raw candidates and a length-term score swap."""
from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

from audit_selected_lengths import COMMIT, proof_length, read_input

PROMPTS = ("P1", "P2", "P3")


def load_rows(name: str, input_dir: Path | None) -> list[dict]:
    data = read_input(name, input_dir)
    if name.endswith("jsonl"):
        return [json.loads(line) for line in data.splitlines() if line]
    return json.loads(data)


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def audit(input_dir: Path | None) -> tuple[list[dict], list[dict], dict]:
    reference = load_rows("benchmark_data_warmup.jsonl", input_dir)
    candidates = load_rows("candidates.jsonl", input_dir)
    results = load_rows("results.json", input_dir)
    expected_keys = {(i, prompt) for i in range(1, 16) for prompt in PROMPTS}
    candidate_by_key = {(row["problem_id"], row["prompt_id"]): row for row in candidates}
    result_by_key = {(row["problem_id"], row["prompt"]): row for row in results}
    if len(reference) != 15 or len(candidates) != 45 or len(results) != 45:
        raise ValueError("expected 15 reference rows and 45 candidate/result rows")
    if set(candidate_by_key) != expected_keys or set(result_by_key) != expected_keys:
        raise ValueError("candidate/result IDs do not form a 15 × 3 grid")

    raw_rows = []
    comparable: dict[int, list[tuple[str, float, float]]] = {}
    score_mismatch: set[int] = set()
    for problem_id in range(1, 16):
        ref = reference[problem_id - 1]
        baseline = proof_length(ref["src"], ref["statement"])
        if baseline != ref["proof_length"]:
            raise ValueError(f"P{problem_id}: official baseline mismatch")
        for prompt in PROMPTS:
            candidate = candidate_by_key[(problem_id, prompt)]
            result = result_by_key[(problem_id, prompt)]
            if candidate["name"] != ref["name"] or result["name"] != ref["name"]:
                raise ValueError(f"P{problem_id}/{prompt}: theorem name mismatch")
            original = proof_length(ref["statement"] + " := " + candidate["original_body"], ref["statement"])
            if original != baseline:
                raise ValueError(f"P{problem_id}/{prompt}: frozen original differs from benchmark")
            tokens = proof_length(ref["statement"] + " := " + candidate["proof_body"], ref["statement"])
            length_delta = tokens - baseline
            local_delta = result["candidate_tokens"] - result["local_baseline_tokens"]
            eligible = result["raw_outcome"] not in ("invalid", "unchanged_user_excluded")
            raw_rows.append({
                "problem_id": problem_id,
                "prompt_id": prompt,
                "raw_outcome": result["raw_outcome"],
                "reference_tokens": baseline,
                "raw_tokens": tokens,
                "proof_length_delta": length_delta,
                "local_o200k_delta": local_delta,
                "strict_direction_reversal": eligible and length_delta * local_delta < 0,
            })
            if not eligible:
                continue
            if result["raw_score"] is None or result["candidate_heartbeat"] is None:
                score_mismatch.add(problem_id)
                continue
            # PR #19's formula: mean of length reduction, heartbeat reduction,
            # and version pass rate. Valid raw candidates here passed all versions.
            reconstructed = (
                100 * (1 - result["candidate_tokens"] / result["local_baseline_tokens"])
                + 100 * (1 - result["candidate_heartbeat"] / result["local_baseline_heartbeat"])
                + 100
            ) / 3
            if abs(reconstructed - result["raw_score"]) > 1e-6:
                score_mismatch.add(problem_id)
                continue
            swapped = result["raw_score"] + (100 / 3) * (
                result["candidate_tokens"] / result["local_baseline_tokens"] - tokens / baseline
            )
            comparable.setdefault(problem_id, []).append((prompt, result["raw_score"], swapped))

    sensitivity_rows = []
    for problem_id in range(1, 16):
        if problem_id in score_mismatch or not comparable.get(problem_id):
            continue
        baseline_choice = ("original", 100 / 3, 100 / 3)
        options = [baseline_choice, *comparable[problem_id]]
        before = max(options, key=lambda row: row[1])
        after = max(options, key=lambda row: row[2])
        sensitivity_rows.append({
            "problem_id": problem_id,
            "reported_raw_winner": before[0],
            "length_term_swap_winner": after[0],
            "reported_winner_score": f"{before[1]:.6f}",
            "swapped_winner_score": f"{after[2]:.6f}",
            "winner_changed": before[0] != after[0],
        })

    valid = [row for row in raw_rows if row["raw_outcome"] not in ("invalid", "unchanged_user_excluded")]
    summary = {
        "source_commit": COMMIT,
        "official_reference_checks": 15,
        "frozen_original_body_checks": 45,
        "raw_candidates": 45,
        "invalid_raw": sum(row["raw_outcome"] == "invalid" for row in raw_rows),
        "excluded_control": sum(row["raw_outcome"] == "unchanged_user_excluded" for row in raw_rows),
        "valid_non_excluded_raw": len(valid),
        "valid_shorter": sum(row["proof_length_delta"] < 0 for row in valid),
        "valid_longer": sum(row["proof_length_delta"] > 0 for row in valid),
        "valid_same": sum(row["proof_length_delta"] == 0 for row in valid),
        "strict_direction_reversals": [[row["problem_id"], row["prompt_id"]] for row in valid if row["strict_direction_reversal"]],
        "score_sensitivity_problems": len(sensitivity_rows),
        "score_sensitivity_excluded": sorted(set(range(1, 16)) - {row["problem_id"] for row in sensitivity_rows}),
        "score_winner_changes": [row["problem_id"] for row in sensitivity_rows if row["winner_changed"]],
    }
    return raw_rows, sensitivity_rows, summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--input-dir", type=Path, help="directory holding the pinned source files")
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    raw, sensitivity, summary = audit(args.input_dir)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    write_csv(args.output_dir / "raw_candidate_metrics.csv", raw)
    write_csv(args.output_dir / "score_sensitivity.csv", sensitivity)
    (args.output_dir / "raw_audit_summary.json").write_text(
        json.dumps(summary, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
