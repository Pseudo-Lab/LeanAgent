"""Run from the repository root: python3 -m week4.lean_repair --help."""
import argparse
from datetime import datetime
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from zoneinfo import ZoneInfo

from .contracts import StatementMismatch, TaskConfigurationError, TaskSpec, digest, write_json
from .controller import Controller
from .lean import LeanVerifier
from .model import ApiBudget, ModelError, OpenRouterModel
from .runtime import ProcessRunner, Trace


def initialize(args):
    source, project = args.source.resolve(), args.project.resolve()
    text = source.read_text()
    if text.count(args.declaration_marker) != 1:
        raise ValueError("declaration marker must occur exactly once")
    start = text.index(args.declaration_marker)
    marker_at = text.index(args.body_start_marker, start)
    if not args.body_start_marker.endswith("by"):
        raise ValueError("body-start-marker must end with by")
    body_start = marker_at + len(args.body_start_marker) - 2
    if args.body_end_marker and text[body_start:].count(args.body_end_marker) != 1:
        raise ValueError("body-end-marker must occur exactly once after the proof starts")
    end = text.index(args.body_end_marker, body_start) if args.body_end_marker else len(text)
    # Keep the newline separating the proof from later commands in the FIXED suffix.
    while end > body_start and text[end - 1].isspace():
        end -= 1
    if end <= body_start:
        raise ValueError("empty proof span")
    manifest = project / "lake-manifest.json"
    head = subprocess.run(["git", "-C", str(project), "rev-parse", "HEAD"], capture_output=True, text=True)
    config = {"task_id": args.task_id or args.target, "source": os.path.relpath(source, args.output.resolve().parent),
              "project": os.path.relpath(project, args.output.resolve().parent), "target": args.target,
              "span": {"declaration_start": start, "body_start": body_start, "body_end": end},
              "pins": {"source_sha256": digest(source.read_bytes()),
                       "fixed_context": {"prefix_chars": body_start, "suffix_chars": len(text)-end,
                                         "prefix_sha256": digest(text[:body_start]), "suffix_sha256": digest(text[end:])},
                       "toolchain": (project / "lean-toolchain").read_text().strip(),
                       "project_commit": head.stdout.strip() if head.returncode == 0 else None,
                       "manifest_sha256": digest(manifest.read_bytes()) if manifest.exists() else None},
              "limits": {"repair_calls": 3, "lean_seconds": 300, "model_seconds": 300,
                         "task_seconds": 1800, "setup_seconds": 600, "max_heartbeats": 200000,
                         "api_usd": "3", "infra_retries": 1},
              "model": {"model": "REPLACE_WITH_OPENROUTER_MODEL_ID", "max_output_tokens": 2048}}
    if args.reference:
        config["reference"] = os.path.relpath(args.reference.resolve(), args.output.resolve().parent)
        config["pins"]["reference_sha256"] = digest(args.reference.read_bytes())
    if args.output.exists():
        raise ValueError("choose a new task configuration path")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=args.output.parent, suffix=".json", delete=False) as stream:
        temporary = Path(stream.name)
    try:
        write_json(temporary, config)
        TaskSpec.load(temporary)
        os.replace(temporary, args.output)
    finally:
        temporary.unlink(missing_ok=True)
    print(args.output)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    init = sub.add_parser("init", help="pin an existing theorem and editable proof span")
    for name in ("source", "project", "output"):
        init.add_argument("--" + name, type=Path, required=True)
    init.add_argument("--target", required=True)
    init.add_argument("--task-id")
    init.add_argument("--declaration-marker", required=True, help="complete command start, including attributes/private if present")
    init.add_argument("--body-start-marker", default=":= by")
    init.add_argument("--body-end-marker", help="literal unique suffix boundary; omit only if the proof ends at EOF")
    init.add_argument("--reference", type=Path, help="optional correct proof with identical fixed prefix/suffix")
    for name in ("check", "run"):
        command = sub.add_parser(name, help="local verification only" if name == "check" else "repair using billed OpenRouter calls")
        command.add_argument("--task", type=Path, required=True)
        command.add_argument("--output", type=Path, help="new directory; existing output is never overwritten")
        command.add_argument("--backend", choices=("cli", "repl"), help="override the task's verifier backend")
        command.add_argument("--repl-command", help="JSON argv for a matching community REPL binary; no shell")
        if name == "check":
            command.add_argument("--proof-body", type=Path, help="check this complete by proof instead of the task input")
    report = sub.add_parser("report", help="aggregate per-problem API spend, including failed calls")
    report.add_argument("results", nargs="+", type=Path)
    args = parser.parse_args(argv)
    trace, budget, task = None, None, None
    try:
        if args.command == "init":
            failure_dir = args.output.resolve().with_name(args.output.name + ".registration")
            # Registration failures are recorded just like failures after task loading.
            trace = Trace(failure_dir.with_name(failure_dir.name + "." + datetime.now(ZoneInfo("Asia/Seoul")).strftime("%Y%m%dT%H%M%S%f")))
            initialize(args)
            # Keep a compact registration event for provenance; no model or Lean was run.
            trace.emit("registered", task_config=str(args.output.resolve()))
            return 0
        if args.command == "report":
            from decimal import Decimal
            rows = [json.loads(p.read_text()) for p in args.results]
            groups = {}
            for row in rows:
                key = row["task_id"]
                if row.get("api_budget") is None:
                    groups.setdefault(key, None)
                else:
                    groups[key] = max(groups.get(key) or Decimal(0), Decimal(row["api_budget"]["committed_usd"]))
            costs = [cost for cost in groups.values() if cost is not None]
            missing = [name for name, cost in groups.items() if cost is None]
            print(json.dumps({"problems": {k: str(v) if v is not None else None for k, v in groups.items()},
                              "total_usd": None if missing else str(sum(costs)),
                              "known_total_usd": str(sum(costs)),
                              "mean_usd": None if missing else str(sum(costs)/len(costs)),
                              "max_usd": None if missing else str(max(costs)),
                              "unknown_problem_costs": missing,
                              "accounting_uncertain": bool(missing) or any(r.get("api_budget") and r["api_budget"]["accounting_uncertain"] for r in rows),
                              "basis": "latest cumulative per-problem ledger; includes unresolved reservations"}, indent=2))
            return 0
        out = args.output or Path(__file__).resolve().parent.parent / "runs" / datetime.now(ZoneInfo("Asia/Seoul")).strftime("%Y%m%dT%H%M%S%f%z")
        trace = Trace(out)
        task = TaskSpec.load(args.task)
        backend = dict(task.config.get("backend") or {"kind": "cli"})
        if args.backend:
            backend["kind"] = args.backend
        if args.repl_command:
            backend["command"] = json.loads(args.repl_command)
        if not isinstance(backend.get("kind", "cli"), str) or backend.get("kind", "cli") not in {"cli", "repl"}:
            raise ValueError("unknown verifier backend")
        task.config["backend"] = backend
        budget = ApiBudget({"limit_usd": task.limits.get("api_usd", "3"),
                            "max_calls": task.limits["repair_calls"],
                            "max_model_tokens": task.limits.get("model_tokens"),
                            "task_id": task.task_id,
                            **({"ledger_path": str(Path(__file__).resolve().parent.parent / "budgets" / (digest(task.task_id)[:24] + ".json"))} if args.command == "run" else {})})
        try:
            write_json(trace.directory / "task.json", task.config)
            write_json(trace.directory / "source.json", {"source_sha256": digest(task.text), "span": task.config["span"]})
            runner = ProcessRunner(trace, task.limits["setup_seconds"])
            model = OpenRouterModel(task.config["model"]) if args.command == "run" else None
            if backend.get("kind") == "repl":
                from .repl import ReplVerifier
                verifier = ReplVerifier(task, runner)
            else:
                verifier = LeanVerifier(task, runner)
            body = args.proof_body.read_text() if args.command == "check" and args.proof_body else None
            result = Controller(task, verifier, model, budget, trace, runner).run(body)
        finally:
            if hasattr(budget, "close"):
                budget.close()
        print(json.dumps({"status": result["status"], "stop_reason": result["stop_reason"],
                          "api_budget": result["api_budget"], "result": str(trace.directory / "result.json")}, ensure_ascii=False, indent=2))
        return 0 if result["status"] == "verified" else 1
    except (OSError, ValueError, KeyError, ModelError) as exc:
        if trace is not None:
            reason = getattr(exc, "stop_reason", None) or ("environment_error" if isinstance(exc, OSError) else "config_error")
            task_id = task.task_id if task else str(getattr(args, "task", getattr(args, "target", "unknown")))
            result = {"task_id": task_id, "status": "stopped", "stop_reason": reason,
                      "detail": str(exc), "attempts": [], "api_requests_this_run": 0,
                      "api_budget": budget.snapshot() if budget else None}
            write_json(trace.directory / "result.json", result)
            trace.emit("stop", **result)
        print(str(exc), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
