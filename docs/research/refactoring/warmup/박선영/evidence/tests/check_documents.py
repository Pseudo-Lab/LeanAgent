"""Check saved evidence and documentation without executing Lean or downloading anything."""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[7]
PERSONAL = ROOT / "docs/research/refactoring/warmup/박선영"
OUTPUT = PERSONAL / "evidence/metrics"
CHECK_OUTPUT = OUTPUT / "local-checks"
checks = []


def check(name, passed):
    checks.append({"name": name, "passed": bool(passed)})


def sha(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def main():
    # Keep fresh checks separate from preserved historical measurement records.
    CHECK_OUTPUT.mkdir(parents=True, exist_ok=True)
    (CHECK_OUTPUT / "repository-checks.json").write_text(json.dumps({"status": "running"}) + "\n")
    # These tests mock subprocess calls; no Lean checkout is executed.
    tests = subprocess.run([sys.executable, "-I", "-m", "unittest", "discover", "-s",
                            str(PERSONAL / "evidence/tests"), "-v"], cwd=ROOT,
                           capture_output=True, text=True)
    (CHECK_OUTPUT / "unit-tests.log").write_text(tests.stdout + tests.stderr)
    check("Python regression suite", tests.returncode == 0)
    documents = [ROOT / "docs/STRUCTURE.md", ROOT / "docs/research/refactoring/warmup/README.md",
                 OUTPUT / "README.md", PERSONAL / "README.md", PERSONAL / "report.md",
                 ROOT / "docs/meetings/2026-10-11-week2/README.md",
                 PERSONAL / "week4-speaker-notes.md",
                 PERSONAL / "evidence/performance-search-2026-10-25/report.md",
                 PERSONAL / "evidence/performance-search-2026-10-25/protocol.md"]
    for document in documents:
        text = re.sub(r"```.*?```", "", document.read_text(), flags=re.DOTALL)
        for href in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
            if re.match(r"(?:https?://|mailto:)", href):
                continue
            filename, _, anchor = href.partition("#")
            target = (document.parent / filename).resolve() if filename else document
            check(f"link {document.relative_to(ROOT)} -> {href}", target.exists())
            if anchor and target.is_file() and target.suffix == ".md":
                headings = re.findall(r"^#{1,6}\s+(.+)$", target.read_text(), re.MULTILINE)
                slugs = [re.sub(r"[^\w\- ]", "", h.lower().replace("`", "")).replace(" ", "-")
                         for h in headings]
                check(f"anchor {href}", anchor in slugs)
    metrics = json.loads((OUTPUT / "metrics.json").read_text())
    report = (PERSONAL / "report.md").read_text()
    for item in metrics["problems"]:
        for run in item["attempts"]:
            text = (ROOT / run["candidate"]).read_text().rstrip("\n")
            check(f"P{item['problem']} run hash", sha(text) == run["candidate_sha256"])
            if run["label"] == "reference" and run["version"] == "v4.31.0":
                check(f"P{item['problem']} report token count", f"{run['proof_tokens']:,}" in report)
                check(f"P{item['problem']} report heartbeat", f"{run['heartbeat']:,}" in report)
        for draft in item["draft_candidates"]:
            check(f"P{item['problem']} draft hash", sha((ROOT / draft["path"]).read_text().rstrip("\n")) == draft["sha256"])
            check(f"P{item['problem']} report draft tokens", f"{draft['proof_tokens']:,}" in report)
        for pair in item["versions"]:
            candidate = pair["candidate"]
            if not candidate or candidate["status"] != "passed":
                continue
            check(f"P{item['problem']} report candidate heartbeat", f"{candidate['heartbeat']:,}" in report)
            check(f"P{item['problem']} report candidate tokens", f"{candidate['proof_tokens']:,}" in report)
            for key in ("token_reduction_pct", "heartbeat_reduction_pct"):
                value = pair[key]
                check(f"P{item['problem']} report {key}", value is not None and f"{abs(value):.2f}%" in report)
    provenance = json.loads((PERSONAL / "evidence/benchmark-provenance.json").read_text())
    check("benchmark provenance hash", sha((PERSONAL / "evidence/benchmark.jsonl").read_text()) == provenance["sha256"])
    loader = importlib.util.spec_from_file_location("document_runner", PERSONAL / "evidence/run_experiments.py")
    runner = importlib.util.module_from_spec(loader)
    loader.loader.exec_module(runner)
    begin, end = runner.MARKERS
    page = (PERSONAL / "presentation-history-2026-10-25.html").read_text()
    actual = page.split(begin, 1)[1].split(end, 1)[0].strip()
    check("HTML table matches metrics", actual == runner.render_table(metrics))
    diff = subprocess.run(["git", "diff", "--check"], cwd=ROOT, capture_output=True, text=True)
    check("git diff --check", diff.returncode == 0)
    # git diff ignores untracked files; check newly authored text files too.
    new_files = list((PERSONAL / "evidence").rglob("*.py")) + list((PERSONAL / "evidence").rglob("*.cjs"))
    new_files += [PERSONAL / "report.md", OUTPUT / "README.md"]
    for path in new_files:
        check(f"whitespace {path.relative_to(ROOT)}", all(line == line.rstrip() for line in path.read_text().splitlines()))
    count = re.search(r"Ran (\d+) tests", tests.stdout + tests.stderr)
    result = {"checked_at": datetime.now(timezone.utc).isoformat(), "checks": checks,
              "status": "passed" if all(c["passed"] for c in checks) else "failed",
              "unit_tests": int(count[1]) if count else None,
              "lean_candidate_execution": "See saved runs in metrics.json; this check does not rerun Lean."}
    (CHECK_OUTPUT / "repository-checks.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "checks": len(checks),
                      "failures": [c["name"] for c in checks if not c["passed"]]}, ensure_ascii=False))
    return 0 if result["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
