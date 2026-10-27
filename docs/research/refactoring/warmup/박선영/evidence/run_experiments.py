#!/usr/bin/env python3
"""Reproduce P8/P11 experiments; keep measurements in this author's evidence/metrics/."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import html
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
OUTPUT = HERE / "metrics"
SHARED = HERE.parent.parent / "정소미/evidence"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MARKERS = ("<!-- experiment-results:start -->", "<!-- experiment-results:end -->")


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# Reuse the reviewed tokenizer and upload-filter definitions, not copies.
tokens = load_module("proof_tokens", SHARED / "proof_tokens.py")
verifier = load_module("warmup_shared_verifier", SHARED / "verify_candidate.py")


def stamp() -> str:
    return datetime.now(timezone.utc).isoformat()


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def relative(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def rows() -> list[dict]:
    return [json.loads(line) for line in (HERE / "benchmark.jsonl").read_text().splitlines()
            if line.strip()]


def problem(number: int) -> dict:
    if number not in (3, 6, 8, 11, 12):
        raise ValueError("Only warm-up 3, 6, 8, 11 and 12 are supported")
    return rows()[number - 1]


def prepare(benchmark: Path) -> None:
    raw = benchmark.read_text(encoding="utf-8")
    data = [json.loads(line) for line in raw.splitlines() if line.strip()]
    if len(data) != 15:
        raise ValueError("Expected the 15-row warm-up benchmark")
    for row in data:
        if tokens.proof_length(row["src"], row["statement"]) != row["proof_length"]:
            raise ValueError(f"Tokenizer does not reproduce baseline: {row['name']}")
    (HERE / "benchmark.jsonl").write_text(raw, encoding="utf-8")
    write_json(HERE / "benchmark-provenance.json", {
        "copied_at": stamp(), "sha256": digest(raw), "rows": len(data),
        "source": "https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena/raw/main/benchmark_data_warmup.jsonl",
        "note": "Existing local snapshot obtained 2026-10-10; not fetched anew. All 15 proof lengths reproduced.",
    })
    for number in (8, 11):
        folder = HERE / f"P{number}"
        folder.mkdir(parents=True, exist_ok=True)
        (folder / "attempts").mkdir(exist_ok=True)
        for filename, text in (("statement.lean", data[number - 1]["statement"]),
                               ("reference.lean", data[number - 1]["src"])):
            path = folder / filename
            if path.exists():
                raise ValueError(f"Refusing to overwrite {path}")
            path.write_text(text.rstrip("\n") + "\n", encoding="utf-8")


def command(args: list[str], cwd: Path, timeout: int) -> dict:
    start = time.monotonic()
    try:
        proc = subprocess.run(args, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return {"exit_code": proc.returncode, "status": "finished",
                "seconds": round(time.monotonic() - start, 3),
                "stdout": proc.stdout, "stderr": proc.stderr}
    except subprocess.TimeoutExpired as exc:
        def text(value):
            return value.decode(errors="replace") if isinstance(value, bytes) else value or ""
        return {"exit_code": None, "status": "timeout",
                "seconds": round(time.monotonic() - start, 3),
                "stdout": text(exc.stdout), "stderr": text(exc.stderr)}


def git(repo: Path, *args: str) -> str:
    result = command(["git", *args], repo, 30)
    if result["exit_code"] != 0:
        raise ValueError(result["stderr"] or "git command failed")
    return result["stdout"].strip()


def validate_environment(repo: Path, row: dict) -> tuple[str, str]:
    if git(repo, "remote", "get-url", "origin").removesuffix(".git") != row["url"].removesuffix(".git"):
        raise ValueError("Checkout origin differs from benchmark")
    revision = git(repo, "rev-parse", "HEAD")
    versions = {commit: version for item in row["version_info"] for version, commit in item.items()}
    if revision not in versions:
        raise ValueError("Checkout revision is not an official problem version")
    version = versions[revision]
    if (repo / "lean-toolchain").read_text().strip() != f"leanprover/lean4:{version}":
        raise ValueError("Pinned revision and Lean toolchain disagree")
    if git(repo, "status", "--porcelain", "--untracked-files=no"):
        raise ValueError("Checkout has tracked changes; refusing to reuse it")
    return version, revision


def validate_candidate(candidate: str, statement: str) -> list[str]:
    if not candidate.startswith(statement):
        raise ValueError("Benchmark statement changed")
    rest = candidate[len(statement):]
    if not re.match(r"\s*:=\s*by(?:\s|$)", rest):
        raise ValueError("Expected unchanged statement followed by := by")
    body = rest.split(":=", 1)[1].lstrip()
    if any(line.strip() and not line[0].isspace() for line in body.splitlines()[1:]):
        raise ValueError("Proof body contains an unindented top-level command")
    stripped = tokens.remove_comments(body)
    forbidden = [name for name, pattern in verifier.FORBIDDEN if re.search(pattern, stripped)]
    if re.search(r"\b(?:run_tac|theorem|lemma)\b", stripped):
        forbidden.append("extra declaration or executable tactic")
    return forbidden


def splice(source: str, original: str, candidate: str) -> str:
    if not original or source.count(original) != 1:
        raise ValueError("Original declaration must occur exactly once in pinned source")
    return source.replace(original, candidate, 1)


def axioms(log: str, name: str) -> list[str] | None:
    pattern = rf"^'{re.escape(name)}' depends on axioms:\s*\[([^\]]*)\]"
    matches = re.findall(pattern, log, re.MULTILINE)
    empty = re.findall(rf"^'{re.escape(name)}' does not depend on any axioms\s*$", log, re.MULTILINE)
    if len(matches) + len(empty) != 1:
        return None
    if empty:
        return []
    return sorted(part.strip() for part in matches[0].split(",") if part.strip())


def valid_check(run: dict, log: str, dependencies: list[str] | None) -> bool:
    return (run["exit_code"] == 0 and ": error" not in log
            and dependencies is not None and set(dependencies) <= ALLOWED_AXIOMS)


def heartbeat_source(source: str, candidate: str) -> str:
    start = source.index(candidate)
    prefix = source[:start]
    # A doc comment or `omit ... in` belongs to the same declaration command.
    if prefix.rstrip().endswith("-/"):
        doc = prefix.rfind("/--")
        if doc >= 0 and prefix[doc:].count("-/") == 1:
            start = doc
    line_start = source.rfind("\n", 0, start) + 1
    previous = source[:line_start].rstrip("\n").split("\n")[-1]
    if previous.lstrip().startswith("omit ") and previous.rstrip().endswith(" in"):
        start = source.rfind(previous, 0, line_start)
    source = source[:start] + "set_option Elab.async false in\n#count_heartbeats in\n" + source[start:]
    lines = source.splitlines()
    imports = [i for i, line in enumerate(lines) if verifier.IMPORT_RE.match(line)]
    if not imports:
        raise ValueError("No import block found")
    lines.insert(max(imports) + 1, "import Mathlib.Util.CountHeartbeats")
    return "\n".join(lines) + "\n"


def measured_heartbeat(run: dict) -> int | None:
    counts = verifier.HB_RE.findall(run["stdout"] + run["stderr"])
    if run["exit_code"] != 0 or len(counts) != 1 or ": error" in run["stdout"] + run["stderr"]:
        return None
    return int(counts[0])


def evaluate(args, output_dir: Path | None = None) -> dict:
    """Evaluate once; callers may isolate output from the legacy presentation runs."""
    row = problem(args.problem)
    if args.problem not in (8, 11) and output_dir is None:
        raise ValueError("Structural pilot problems require an isolated output directory")
    repo = args.repo.resolve()
    candidate_path = args.candidate.resolve()
    candidate = candidate_path.read_text(encoding="utf-8").rstrip("\n")
    statement = row["statement"]
    forbidden = validate_candidate(candidate, statement)
    if forbidden:
        raise ValueError(f"Forbidden patterns: {forbidden}")
    version, revision = validate_environment(repo, row)
    source = (repo / row["file_path"]).read_text(encoding="utf-8")
    original = row["src"].rstrip("\n")
    replay = splice(source, original, candidate)
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ") + "-" + args.label
    output = output_dir if output_dir is not None else OUTPUT / f"P{args.problem}/runs" / run_id
    output.mkdir(parents=True, exist_ok=False)
    result = {"measured_at": stamp(), "problem": args.problem, "name": row["name"],
              "label": args.label, "hypothesis": args.hypothesis,
              "candidate": relative(candidate_path), "candidate_sha256": digest(candidate),
              "reference_sha256": digest(original), "source_sha256": digest(source),
              "source_file": row["file_path"], "repo_url": row["url"],
              "revision": revision, "version": version, "statement_unchanged": True,
              "forbidden_patterns": [], "proof_tokens": tokens.proof_length(candidate, statement),
              "official_reference_tokens": row["proof_length"], "axioms": None,
              "valid": False, "heartbeat": None, "official_worker": False,
              "api_cost_usd": None, "output": relative(output)}
    with tempfile.TemporaryDirectory(prefix=f"leanagent-p{args.problem}-") as scratch:
        scratch = Path(scratch)
        check = scratch / "Check.lean"
        check.write_text(replay + f"\n#print axioms {row['name']}\n", encoding="utf-8")
        run = command(["lake", "env", "lean", str(check)], repo, args.timeout)
        log = run.pop("stdout") + run.pop("stderr")
        (output / "check.log").write_text(log, encoding="utf-8")
        result["check"] = {**run, "command": ["lake", "env", "lean", "<temporary>/Check.lean"]}
        result["axioms"] = axioms(log, row["name"])
        result["valid"] = valid_check(run, log, result["axioms"])
        if result["valid"]:
            hb = scratch / "Heartbeat.lean"
            hb.write_text(heartbeat_source(replay, candidate), encoding="utf-8")
            measurement = command(["lake", "env", "lean", str(hb)], repo, args.timeout)
            result["heartbeat"] = measured_heartbeat(measurement)
            hb_log = measurement.pop("stdout") + measurement.pop("stderr")
            (output / "heartbeat.log").write_text(hb_log, encoding="utf-8")
            result["measurement"] = {**measurement,
                "command": ["lake", "env", "lean", "<temporary>/Heartbeat.lean"]}
    result["status"] = ("passed" if result["valid"] and result["heartbeat"] is not None
                        else "measurement_failed" if result["valid"] else result["check"]["status"]
                        if result["check"]["status"] == "timeout" else "failed")
    write_json(output / "result.json", result)
    return result


def verify(args) -> int:
    result = evaluate(args)
    print(json.dumps({key: result[key] for key in
                      ("problem", "label", "version", "status", "proof_tokens", "heartbeat", "output")}, ensure_ascii=False))
    return 0 if result["status"] == "passed" else 1


def reduction(before, after):
    return round(100 * (1 - after / before), 4) if before and after is not None else None


def aggregate() -> dict:
    summaries = []
    drafts = json.loads((HERE / "candidates.json").read_text(encoding="utf-8"))
    for number in (8, 11):
        row = problem(number)
        history = [json.loads(path.read_text()) for path in sorted((OUTPUT / f"P{number}/runs").glob("*/result.json"))]
        versions = [v for item in row["version_info"] for v in item]
        selected_path = HERE / f"P{number}/selected.lean"
        selected_hash = digest(selected_path.read_text().rstrip("\n")) if selected_path.exists() else None
        candidates = []
        for draft in drafts:
            if draft["problem"] != number:
                continue
            path = HERE / draft["path"]
            text = path.read_text(encoding="utf-8").rstrip("\n")
            forbidden = validate_candidate(text, row["statement"])
            candidate_hash = digest(text)
            validated_versions = sorted({run["version"] for run in history
                if run["candidate_sha256"] == candidate_hash and run["valid"]})
            candidates.append({**draft, "path": relative(path), "sha256": candidate_hash,
                "proof_tokens": tokens.proof_length(text, row["statement"]),
                "statement_unchanged": True, "forbidden_patterns": forbidden,
                "static_checks_only": not validated_versions,
                "validated_versions": validated_versions})
        comparisons = []
        for version in versions:
            baseline = next((run for run in reversed(history) if run["version"] == version
                             and run["label"] == "reference" and run["candidate_sha256"] == digest(row["src"].rstrip("\n"))), None)
            candidate = next((run for run in reversed(history) if run["version"] == version
                              and run["candidate_sha256"] == selected_hash), None) if selected_hash else None
            comparisons.append({"version": version, "reference": baseline, "candidate": candidate,
                "token_reduction_pct": reduction(baseline["proof_tokens"], candidate["proof_tokens"])
                    if baseline and candidate and baseline["status"] == candidate["status"] == "passed" else None,
                "heartbeat_reduction_pct": reduction(baseline["heartbeat"], candidate["heartbeat"])
                    if baseline and candidate and baseline["status"] == candidate["status"] == "passed" else None})
        passed = sum(bool(pair["candidate"] and pair["candidate"]["valid"]
                          and pair["reference"] and pair["reference"]["valid"]
                          and set(pair["candidate"]["axioms"]) <= set(pair["reference"]["axioms"])) for pair in comparisons)
        summaries.append({"problem": number, "name": row["name"],
            "selected": relative(selected_path) if selected_hash else None,
            "selected_sha256": selected_hash, "draft_candidates": candidates, "versions": comparisons,
            "compatibility": {"passed": passed, "required": len(versions),
                              "tested": sum(bool(pair["candidate"]) for pair in comparisons)},
            "attempts": history})
    availability = OUTPUT / "environment-status.json"
    return {"generated_at": stamp(), "official_worker": False, "api_cost_usd": None,
            "note": "Local measurements, not official scores. Proof tokens are computed statically; candidate validity is tracked separately. Missing versions are not passes. Heartbeats compare only within the same version.",
            "environment_status": json.loads(availability.read_text(encoding="utf-8"))
                if availability.exists() else None,
            "problems": summaries}


def recorded_output_path(output: str) -> Path:
    """Resolve relocated evidence without rewriting historical result JSON."""
    path = Path(output)
    try:
        suffix = path.relative_to("metrics/warmup/박선영")
    except ValueError:
        return ROOT / path
    return OUTPUT / suffix


def render_table(data: dict) -> str:
    lines = ['<div class="scroll"><table><caption>원본 → 선택 후보 · 로컬 측정 / 미검증 초안 토큰은 별도 표기</caption><thead><tr><th>문제 / 환경</th><th>증명 토큰</th><th>heartbeat</th><th>원본 / 후보 상태</th><th>후보 지정 버전 통과</th><th>근거</th></tr></thead><tbody>']
    for item in data["problems"]:
        for pair in item["versions"]:
            baseline, candidate = pair["reference"], pair["candidate"]
            def metric(key, pct):
                a = baseline.get(key) if baseline else None
                b = candidate.get(key) if candidate else None
                text = f"{a:,}" if a is not None else "미측정"
                text += " → " + (f"{b:,}" if b is not None else "미측정")
                if pct is None:
                    return text
                direction = "감소" if pct >= 0 else "증가"
                return text + f" ({abs(pct):.2f}% {direction})"
            compat = item["compatibility"]
            record = candidate or baseline
            link = os.path.relpath(recorded_output_path(record["output"]) / "result.json", HERE.parent) if record else ""
            evidence = f'<a href="{html.escape(link, quote=True)}">실행 기록</a>' if link else "기록 없음"
            states = {"passed": "통과", "failed": "실패", "timeout": "timeout",
                      "measurement_failed": "검증 통과·측정 실패"}
            def status(run):
                return states.get(run["status"], run["status"]) if run else "미실행"
            values = [f"{item['problem']}번 · {pair['version']}",
                      metric("proof_tokens", pair["token_reduction_pct"]),
                      metric("heartbeat", pair["heartbeat_reduction_pct"]),
                      f"{status(baseline)} / {status(candidate)}",
                      f"{compat['passed']}/{compat['required']} (검사 {compat['tested']})"]
            lines.append("<tr>" + "".join(f"<td>{html.escape(value)}</td>" for value in values) + f"<td>{evidence}</td></tr>")
    lines.append("</tbody></table></div>")
    for item in data["problems"]:
        for draft in item.get("draft_candidates", []):
            link = os.path.relpath(ROOT / draft["path"], HERE.parent)
            verified = draft.get("validated_versions", [])
            state = ("Lean 검증 통과: " + ", ".join(verified)) if verified else "정적 계산만 완료, 컴파일·heartbeat 미검증"
            lines.append(f'<p class="source">{item["problem"]}번 후보 '
                         f'<a href="{html.escape(link, quote=True)}">{html.escape(draft["label"])}</a>: '
                         f'{draft["proof_tokens"]:,} tokens ({html.escape(state)}). '
                         f'{html.escape(draft["hypothesis"])}</p>')
    return "\n".join(lines)


def summarize(update_html: bool) -> None:
    data = aggregate()
    write_json(OUTPUT / "metrics.json", data)
    if update_html:
        presentation = HERE.parent / "presentation.html"
        text = presentation.read_text(encoding="utf-8")
        begin, end = MARKERS
        if text.count(begin) != 1 or text.count(end) != 1:
            raise ValueError("Expected exactly one HTML result marker pair")
        before, tail = text.split(begin)
        _, after = tail.split(end)
        presentation.write_text(before + begin + "\n" + render_table(data) + "\n" + end + after,
                                encoding="utf-8")
    print(relative(OUTPUT / "metrics.json"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="action", required=True)
    prep = commands.add_parser("prepare")
    prep.add_argument("--benchmark", required=True, type=Path)
    run = commands.add_parser("verify")
    run.add_argument("--problem", required=True, type=int, choices=(8, 11))
    run.add_argument("--repo", required=True, type=Path)
    run.add_argument("--candidate", required=True, type=Path)
    run.add_argument("--label", required=True)
    run.add_argument("--hypothesis", required=True)
    run.add_argument("--timeout", type=int, default=180)
    summary = commands.add_parser("summarize")
    summary.add_argument("--update-html", action="store_true")
    args = parser.parse_args()
    if args.action == "prepare":
        prepare(args.benchmark)
    elif args.action == "verify":
        if not re.fullmatch(r"[A-Za-z0-9_-]+", args.label):
            parser.error("label must contain only letters, numbers, underscore or hyphen")
        return verify(args)
    else:
        summarize(args.update_html)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError) as exc:
        sys.exit(str(exc))
