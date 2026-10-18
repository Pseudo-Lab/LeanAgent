#!/usr/bin/env python3
"""Recount PR #19's 15 selected proofs with the warm-up proof-length rule.

Inputs are pinned to a Git commit and SHA-256 hashes. By default they are
downloaded from GitHub; --input-dir uses already downloaded copies.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
import urllib.parse
import urllib.request
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from proof_tokens import proof_length  # noqa: E402

COMMIT = "74d2aa111e3594052489a70f1580cf8bed4b25cb"
SOURCE = "docs/research/verifier-guided-agent/남성우/evidence/warmup-2026-10-15"
FILES = {
    "benchmark_data_warmup.jsonl": (
        "reference/benchmark_data_warmup.jsonl",
        "6209680cf00cde0765b77b24834cd72c64dd585b2f7e3f2a58209980ab59a804",
    ),
    "selected.json": (
        "selected.json",
        "ac3a9a1d7617a6cfbe0de5d7b81015b68adb2535c9afe90828c550461ef8a1ef",
    ),
    "results.json": (
        "results.json",
        "3bfe39a977ebc895c895adb35c8d75bb676a8de9132b2c440f31300ca6fa6799",
    ),
}


def read_input(name: str, input_dir: Path | None) -> bytes:
    path, expected_hash = FILES[name]
    if input_dir is None:
        url = "https://raw.githubusercontent.com/Pseudo-Lab/LeanAgent/" + COMMIT + "/"
        url += urllib.parse.quote(SOURCE + "/" + path)
        with urllib.request.urlopen(url, timeout=30) as response:
            data = response.read()
    else:
        data = (input_dir / name).read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != expected_hash:
        raise ValueError(f"{name}: SHA-256 mismatch ({digest})")
    return data


def audit(input_dir: Path | None) -> list[dict[str, object]]:
    benchmark = [json.loads(line) for line in read_input("benchmark_data_warmup.jsonl", input_dir).splitlines() if line]
    selected = json.loads(read_input("selected.json", input_dir))
    results = json.loads(read_input("results.json", input_dir))
    if len(benchmark) != 15 or len(selected) != 15 or {row["problem_id"] for row in selected} != set(range(1, 16)):
        raise ValueError("expected exactly one selected proof for each of the 15 problems")
    by_id = {row["problem_id"]: row for row in selected}
    result_by_key = {(row["problem_id"], row["prompt"]): row for row in results}
    output = []
    for problem_id, reference in enumerate(benchmark, 1):
        choice = by_id[problem_id]
        if reference["name"] != choice["name"]:
            raise ValueError(f"P{problem_id}: theorem name differs")
        original = proof_length(reference["src"], reference["statement"])
        if original != reference["proof_length"]:
            raise ValueError(f"P{problem_id}: official baseline {reference['proof_length']} != local {original}")
        declaration = reference["statement"] + " := " + choice["proof_body"]
        recounted = proof_length(declaration, reference["statement"])
        local_raw_delta: int | str = ""
        if choice["selection"].endswith("/raw"):
            prompt = choice["selection"].split("/", 1)[0]
            reported = result_by_key[(problem_id, prompt)]
            local_raw_delta = reported["candidate_tokens"] - reported["local_baseline_tokens"]
        output.append({
            "problem_id": problem_id,
            "name": choice["name"],
            "selection": choice["selection"],
            "official_reference_tokens": original,
            "recounted_selected_tokens": recounted,
            "recounted_delta": recounted - original,
            "reported_local_raw_delta": local_raw_delta,
            "baseline_complete": choice["baseline_complete"],
        })
    return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--input-dir", type=Path, help="directory holding the three pinned source files")
    args = parser.parse_args()
    rows = audit(args.input_dir)
    writer = csv.DictWriter(sys.stdout, fieldnames=list(rows[0]), lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    shorter = sum(row["recounted_delta"] < 0 for row in rows)
    longer = sum(row["recounted_delta"] > 0 for row in rows)
    print(f"official baselines 15/15; selected shorter={shorter}, longer={longer}, same={15-shorter-longer}", file=sys.stderr)


if __name__ == "__main__":
    main()
