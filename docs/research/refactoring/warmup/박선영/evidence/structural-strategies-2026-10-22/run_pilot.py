#!/usr/bin/env python3
"""Bounded structural pilot; reuse the existing full-file evaluator, no model API."""
import argparse
from datetime import datetime, timezone
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace
import traceback

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("pilot_evaluator", HERE.parent / "run_experiments.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
OUTPUT = HERE.parent / "metrics" / "structural-pilot-2026-10-25"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save_new(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def fingerprint(repo, number):
    row = runner.problem(number)
    version, revision = runner.validate_environment(repo, row)
    files = [Path(__file__), HERE.parent / "run_experiments.py",
             HERE.parent / "benchmark.jsonl", runner.SHARED / "proof_tokens.py",
             runner.SHARED / "verify_candidate.py", repo / "lean-toolchain",
             repo / "lake-manifest.json", repo / row["file_path"]]
    return {"version": version, "revision": revision,
            "files": {str(path): sha(path) for path in files}}


def transform(number, strategy, source):
    lines = source.splitlines(keepends=True)
    if (number, strategy) == (11, "S1"):
        assert "set P₀_coeffs" in lines[114] and "set P₁_coeffs" in lines[119]
        return "".join(lines[:114] + lines[119:])
    if (number, strategy) == (12, "S1"):
        assert "have h_R_star_card_gt_eps" in lines[119]
        assert "exact h_prob_Rstar_gt_eps_div_q" in lines[131]
        return "".join(lines[:119] + lines[132:])
    if (number, strategy) == (11, "S2"):
        assert "_ = P₀.eval" in lines[149] and "_ = P₀.eval" in lines[152]
        return "".join(lines[:149] + lines[152:])
    if (number, strategy) == (11, "S3"):
        original = "    have h2 : 2^(ℓ - (i + 1) + 1) = 2^(ℓ - i) := by rw [h1]\n"
        assert source.count(original) == 2
        marker = "  set P₀_coeffs :="
        assert source.count(marker) == 1
        shared = ("  have h_shared_pow : 2^(ℓ - (i + 1) + 1) = 2^(ℓ - i) := by\n"
                  "    congr 1\n    omega\n")
        # Retain local h1 declarations: removing them would add a second strategy.
        return source.replace(marker, shared + marker).replace(original, "    have h2 := h_shared_pow\n")
    raise ValueError("No preregistered transformation for this pair")


def prepare(repo, number, strategy):
    folder = HERE / f"P{number}-{strategy}"
    if folder.exists():
        raise ValueError("Preparation exists; refusing to overwrite")
    row = runner.problem(number)
    source = row["src"].rstrip("\n")
    hypotheses = {
        (11, "S1"): "Remove only P₀_coeffs; avoid elaborating an unreferenced local definition.",
        (12, "S1"): "Remove only h_R_star_card_gt_eps; its scoped derivation is not referenced later.",
        (11, "S2"): "Skip the expanded intermediate calc equality; connect to the next factored expression using ring.",
        (11, "S3"): "Prove the repeated h2 exponent equality once in common scope; reuse without removing h1.",
    }
    hypothesis = hypotheses[number, strategy]
    frozen = fingerprint(repo, number)
    actual = (repo / row["file_path"]).read_text()
    runner.splice(actual, source, source)
    save_new(folder / "hypothesis.json", {
        "registered_at": datetime.now(timezone.utc).isoformat(),
        "problem": number, "strategy": strategy, "strategy_version": 1,
        "hypothesis": hypothesis, "parent": "benchmark original, not previous best",
        "reference_sha256": runner.digest(source), "fingerprint": frozen,
        "repo": str(repo), "timeout_seconds_per_command": 180,
        "max_candidate_versions": 2, "planned_repetitions_per_body": 2,
        "note": "Repeat identical bodies for measurement; repairs are new candidates. No automatic repair or selection."})
    candidate = transform(number, strategy, source)
    assert candidate != source
    assert not runner.validate_candidate(candidate, row["statement"])
    for name, text in (("reference.lean", source), ("candidate-01.lean", candidate)):
        with (folder / name).open("x") as stream:
            stream.write(text + "\n")
    with (folder / "candidate-01.diff").open("x") as stream:
        stream.write("".join(difflib.unified_diff(source.splitlines(True), candidate.splitlines(True),
                                               fromfile="reference", tofile="candidate-01")))
    save_new(folder / "inputs.json", {name: sha(folder / name) for name in
                                     ("hypothesis.json", "reference.lean", "candidate-01.lean", "candidate-01.diff")})
    print(f"Prepared P{number}-{strategy}", flush=True)


def compare(baseline, candidate):
    keys = ("problem", "name", "version", "revision", "source_sha256", "reference_sha256")
    if any(baseline.get(key) != candidate.get(key) for key in keys):
        return {"status": "environment_mismatch", "improved": False}
    if baseline.get("status") != "passed" or baseline.get("candidate_sha256") != baseline.get("reference_sha256"):
        return {"status": "baseline_unavailable", "improved": False}
    if candidate.get("status") != "passed":
        return {"status": candidate.get("status", "tool_error"), "improved": False}
    if baseline.get("axioms") is None or candidate.get("axioms") is None:
        return {"status": "axioms_missing", "improved": False}
    added = sorted(set(candidate["axioms"]) - set(baseline["axioms"]))
    if added:
        return {"status": "new_axioms", "added": added, "improved": False}
    hb, base = candidate.get("heartbeat"), baseline.get("heartbeat")
    if hb is None or base is None or base <= 0:
        return {"status": "measurement_failed", "improved": False}
    return {"status": "passed", "improved": hb < base,
            "heartbeat_delta": hb - base, "heartbeat_reduction_pct": runner.reduction(base, hb),
            "token_delta": candidate["proof_tokens"] - baseline["proof_tokens"], "added_axioms": []}


def evaluate(number, strategy, kind, repetition):
    folder = HERE / f"P{number}-{strategy}"
    inputs = json.loads((folder / "inputs.json").read_text())
    for name, expected in inputs.items():
        if sha(folder / name) != expected:
            raise ValueError(f"Frozen input changed: {name}")
    plan = json.loads((folder / "hypothesis.json").read_text())
    repo = Path(plan["repo"])
    if fingerprint(repo, number) != plan["fingerprint"]:
        raise ValueError("Environment/evaluator drift; start a new experiment")
    output = OUTPUT / f"P{number}-{strategy}" / f"{kind}-{repetition}"
    if output.exists():
        raise ValueError("Run already exists; refusing overwrite or duplicate execution")
    filename = "reference.lean" if kind == "baseline" else "candidate-01.lean"
    baseline_path = output.parent / f"baseline-{repetition}" / "result.json"
    if kind == "candidate":
        baseline = json.loads(baseline_path.read_text())
        if baseline["status"] != "passed":
            raise ValueError("Baseline not passed; candidate must wait")
    args = SimpleNamespace(problem=number, repo=repo, candidate=folder / filename,
                           label=f"{strategy}-{kind}-{repetition}", hypothesis=plan["hypothesis"],
                           timeout=plan["timeout_seconds_per_command"])
    # Reserve the run before invoking Lean; interruption is visible and not auto-retried.
    save_new(output.parent / f"{kind}-{repetition}.started.json", {
        "started_at": datetime.now(timezone.utc).isoformat(), "inputs": inputs,
        "fingerprint": plan["fingerprint"], "status": "started"})
    try:
        result = runner.evaluate(args, output_dir=output)
        if fingerprint(repo, number) != plan["fingerprint"]:
            raise ValueError("Environment/evaluator changed during execution")
        review = compare(result, result) if kind == "baseline" else compare(baseline, result)
        save_new(output / "review.json", review)
        print(json.dumps({"problem": number, "strategy": strategy, "kind": kind,
                          "repetition": repetition, "heartbeat": result["heartbeat"],
                          "tokens": result["proof_tokens"], **review}), flush=True)
    except Exception as exc:
        save_new(output / "tool-error.json", {"status": "tool_error", "error": str(exc),
                                             "traceback": traceback.format_exc()})
        raise


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("prepare", "evaluate"))
    parser.add_argument("--problem", type=int, choices=(11, 12), required=True)
    parser.add_argument("--strategy", choices=("S1", "S2", "S3"), required=True)
    parser.add_argument("--repo", type=Path)
    parser.add_argument("--kind", choices=("baseline", "candidate"))
    parser.add_argument("--repetition", type=int, choices=(1, 2), default=1)
    args = parser.parse_args()
    if args.action == "prepare":
        if args.repo is None:
            parser.error("prepare requires --repo")
        prepare(args.repo.resolve(), args.problem, args.strategy)
    else:
        if args.kind is None:
            parser.error("evaluate requires --kind")
        evaluate(args.problem, args.strategy, args.kind, args.repetition)
