"""Local CLI adapter. Instrumentation is separate from the final accepted file."""
import json
from pathlib import Path
import re
import subprocess

from .contracts import StatementMismatch, TaskSpec, VerificationResult, digest, write_json
from .diagnostics import (apply_info_feedback, classify_error_status, enrich_diagnostics,
                          map_info_records, parse_cli_output, source_header_end)


class LeanVerifier:
    def __init__(self, task: TaskSpec, runner):
        self.task, self.runner = task, runner
        self.out = runner.trace.directory
        self.environment_id = "not_checked"
        self.environment = None
        self.reference_metrics = None
        self.counter = 0

    def _environment(self):
        """Capture tracked changes as well as revisions; never modify the project."""
        t = self.task
        t.assert_statement()
        if digest(t.source.read_bytes()) != t.config["pins"]["source_sha256"]:
            raise ValueError("input source changed")
        pins = t.config["pins"]
        reference_source = getattr(t, "reference_source", None)
        if reference_source and digest(reference_source.read_bytes()) != pins.get("reference_sha256"):
            raise ValueError("reference source changed")
        toolchain = (t.project / "lean-toolchain").read_text().strip()
        if toolchain != pins["toolchain"]:
            raise ValueError("toolchain mismatch")
        manifest = t.project / "lake-manifest.json"
        lock = digest(manifest.read_bytes()) if manifest.exists() else None
        if lock != pins.get("manifest_sha256"):
            raise ValueError("dependency lock mismatch")
        def git(path, *args):
            call = subprocess.run(["git", "-C", str(path), *args], capture_output=True,
                                  timeout=min(10, max(.01, self.runner.remaining)), check=True)
            return call.stdout
        snapshot = {"toolchain": toolchain, "manifest_sha256": lock}
        if pins.get("project_commit"):
            head = git(t.project, "rev-parse", "HEAD").decode().strip()
            if head != pins["project_commit"]:
                raise ValueError("project commit mismatch")
            snapshot.update(commit=head, tracked_diff=digest(git(t.project, "diff", "HEAD", "--")))
        if manifest.exists():
            data = json.loads(manifest.read_text())
            if not isinstance(data, dict):
                raise ValueError("dependency manifest must be a JSON object")
            packages_dir = data.get("packagesDir", ".lake/packages")
            dependencies = data.get("packages", [])
            if not isinstance(packages_dir, str) or not packages_dir:
                raise ValueError("dependency manifest packagesDir must be a nonempty string")
            if not isinstance(dependencies, list):
                raise ValueError("dependency manifest packages must be a list")
            packages = t.project / packages_dir
            snapshot["dependencies"] = []
            for dep in dependencies:
                if not isinstance(dep, dict):
                    raise ValueError("dependency manifest package entries must be objects")
                if dep.get("type") != "git":
                    raise ValueError("only pinned git dependencies are supported")
                if not all(isinstance(dep.get(key), str) and dep[key] for key in ("name", "rev")):
                    raise ValueError("pinned git dependencies require nonempty string name and rev")
                path = packages / dep["name"].removeprefix("«").removesuffix("»")
                head = git(path, "rev-parse", "HEAD").decode().strip()
                if head != dep["rev"]:
                    raise ValueError("dependency commit mismatch: " + dep["name"])
                snapshot["dependencies"].append({"name": dep["name"], "commit": head,
                                                "tracked_diff": digest(git(path, "diff", "HEAD", "--"))})
        return snapshot

    def _directory(self, label):
        self.counter += 1
        dest = self.out / "lean" / f"{self.counter:03d}_{label}"
        dest.mkdir(parents=True)
        return dest

    def _run(self, text, label, instrumented=False, heartbeat_limit=None):
        dest = self._directory(label)
        file = dest / "candidate.lean"
        file.write_text(text)
        cap = self.task.limits["max_heartbeats"] if heartbeat_limit is None else heartbeat_limit
        flags = ["--json", f"--root={self.out}", f"-DmaxHeartbeats={cap}"]
        if instrumented:
            flags.append("-DElab.async=false")
        # An inherited ELAN_TOOLCHAIN must not silently override the task pin.
        proc = self.runner.run(["elan", "run", self.task.config["pins"]["toolchain"],
                                "lake", "env", "lean", *flags, str(file)], self.task.project,
                               dest, self.task.limits["lean_seconds"])
        messages, unparsed = parse_cli_output(Path(proc["stdout"]).read_text(errors="replace"))
        return dest, proc, messages, unparsed

    @staticmethod
    def _process_status(proc):
        if proc["wall_time_limit"]:
            return "wall_time_limit"
        if proc["timeout"]:
            return "timeout"
        if proc["process_error"] or proc["returncode"] is None or proc["returncode"] < 0:
            return "process_error"
        return None

    @staticmethod
    def _heartbeat_exceeded(messages):
        return any(d["severity"] == "error" and
                   (("maximum number of heartbeats (" in str(d["message"])
                     and "has been reached" in str(d["message"]))
                    or "(kernel) deterministic timeout" in str(d["message"]))
                   for d in messages)

    def _with_support(self, text):
        at = source_header_end(text[:self.task.declaration_start])
        helper = Path(__file__).with_name("Support.lean").read_text().split("import Lean\n", 1)[1]
        # Helper compilation is evaluator overhead, outside the target's resource cap.
        # The section restores the original options before any source command runs.
        return text[:at] + "\nimport Lean\n\nmeta section\nset_option maxHeartbeats 0\n" + helper + "\nend\n" + text[at:]

    def _audit_suffix(self):
        target = "_root_." + self.task.config["target"]
        return f"\n#check {target}\n#print axioms {target}\n"

    def _axioms(self, messages):
        target = self.task.config["target"]
        for diagnostic in reversed(messages):
            match = re.search(r"'([^'\n]+)' (depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                              str(diagnostic["message"]))
            if not match:
                continue
            name = match[1]
            # Private aliases resolve to a file-dependent internal kernel name.
            if name != target and not (name.startswith("_private.") and name.endswith("." + target)):
                continue
            return sorted(x.strip() for x in (match[3] or "").split(",") if x.strip())
        return None

    def prepare(self):
        t = self.task
        result = VerificationResult(t.task_id, "prepare", digest(t.text), self.environment_id,
                                    "environment", "environment_error")
        try:
            self.environment = self._environment()
            self.environment_id = digest(json.dumps(self.environment, sort_keys=True))
            write_json(self.out / "environment.json", self.environment)
            # Trusted incomplete proof probes the ORIGINAL fixed context, without any model code.
            probe = t.assemble("by\n  sorry\n") + self._audit_suffix()
            _, proc, messages, unparsed = self._run(probe, "environment", heartbeat_limit=0)
            result.process_exit_code, result.diagnostics = proc["returncode"], messages
            result.raw_log_path = proc["stdout"]
            failure = self._process_status(proc)
            if failure or proc["returncode"] != 0 or unparsed or any(m["severity"] == "error" for m in messages):
                result.status = failure or "environment_error"
                result.detail = "fixed-context probe failed before any model call"
                return result
            result.environment_id, result.status = self.environment_id, "candidate_pass"
            if t.reference_text is not None:
                reference = self.verify(t.body_from(t.reference_text), "reference", "reference")
                if reference.status != "candidate_pass":
                    reference.status = "environment_error"
                    reference.detail = "reference proof failed; no model called"
                    return reference
                self.reference_metrics = reference.metrics
                write_json(self.out / "reference.json", reference.to_dict())
            return result
        except StatementMismatch as exc:
            result.status, result.statement_check = "statement_mismatch", "mismatch"
            result.failure_kind, result.detail = "statement_mismatch", str(exc)
            return result
        except (OSError, ValueError, subprocess.SubprocessError) as exc:
            result.detail = str(exc)
            return result

    def _context(self, text, diagnostics, label):
        """Replay the target command with native InfoTree collection, never accepted code."""
        at = self.task.declaration_start
        instrumented = self._with_support(text[:at] + "#repair_context\n" + text[at:])
        added = len(instrumented.encode()) - len(text.encode())
        dest, proc, messages, unparsed = self._run(instrumented, label + "_context", True)
        records, reason = [], None
        try:
            payloads = [m["message"].split("|", 1)[1] for m in messages
                        if str(m["message"]).startswith("REPAIR_CONTEXT|")]
            if self._process_status(proc) or unparsed or len(payloads) != 1:
                reason = "native InfoTree replay unavailable; inspect " + proc["stdout"]
            else:
                records = map_info_records(json.loads(payloads[0]), text, added)
        except (TypeError, ValueError):
            reason = "invalid native InfoTree payload; inspect " + proc["stdout"]
        goals, contexts, sorries = apply_info_feedback(diagnostics, records)
        if reason:
            for diagnostic in diagnostics:
                if diagnostic.get("severity") == "error" and diagnostic.get("goals") is None:
                    diagnostic["context_unavailable_reason"] = reason
        write_json(dest / "proof_info.json", {"records": records, "unavailable_reason": reason})
        return goals, contexts, sorries

    def verify(self, body, attempt, check_kind="candidate"):
        t = self.task
        result = VerificationResult(t.task_id, attempt, digest(t.assemble(body)) if isinstance(body, str) else "",
                                    self.environment_id,
                                    check_kind, "invalid_candidate")
        try:
            t.assert_statement()
            if self._environment() != self.environment:
                result.status, result.detail = "environment_error", "fixed environment changed"
                return result
            if not isinstance(body, str) or not body.startswith("by") or len(body.encode()) > 100000:
                result.detail = "candidate must be one complete by proof, at most 100000 bytes"
                result.failure_kind = "syntax"
                return result
            # Guard is parse-only. Its separate file elaborates only a trusted sorry placeholder.
            heartbeat_limit = 0 if check_kind == "reference" else None
            guard = (t.text[:t.declaration_start] + "#repair_guard " + json.dumps(body, ensure_ascii=False) + "\n"
                     + t.text[t.declaration_start:t.body_start] + "by\n  sorry\n" + t.text[t.body_end:])
            _, gp, gm, gu = self._run(self._with_support(guard), attempt + "_guard", True,
                                    heartbeat_limit=0)
            counts = [int(m["message"].split("|", 1)[1]) for m in gm
                      if str(m["message"]).startswith("REPAIR_GUARD|")]
            # Only the exact trusted input may bypass a policy rejection to collect
            # real compiler feedback. An alternative --proof-body is still guarded.
            guard_failure = self._process_status(gp)
            guard_rejected = gp["returncode"] != 0 or gu or len(counts) != 1
            trusted_initial = attempt == "initial" and body == t.initial_body
            if guard_failure or (guard_rejected and not trusted_initial):
                result.status = guard_failure or "invalid_candidate"
                result.diagnostics, result.raw_log_path = gm, gp["stdout"]
                result.detail = "parse-only proof boundary/policy check failed"
                result.failure_kind = "policy" if any("forbidden syntax or identifier" in str(m["message"]) for m in gm) else "syntax"
                return result
            result.metrics["proof_tokens"] = counts[0] if counts else None
            max_tokens = t.limits.get("proof_tokens")
            if check_kind != "reference" and counts and max_tokens is not None and counts[0] > max_tokens:
                result.status, result.detail = "resource_limit", "proof token limit exceeded"
                return result
            text = t.assemble(body)
            t.assert_statement(text)
            dest, proc, messages, unparsed = self._run(text + self._audit_suffix(), attempt,
                                                      heartbeat_limit=heartbeat_limit)
            result.process_exit_code, result.elapsed_ms = proc["returncode"], proc["elapsed_ms"]
            result.diagnostics, result.raw_log_path = messages, proc["stdout"]
            result.statement_check = "fixed_context_preserved"
            result.axioms = self._axioms(messages)
            enrich_diagnostics(messages, text)
            failure = self._process_status(proc)
            if failure:
                result.status = failure
            elif self._heartbeat_exceeded(messages):
                result.status, result.detail = "resource_limit", "Lean maxHeartbeats exceeded"
            elif classify_error_status(messages):
                result.status = classify_error_status(messages)
                result.failure_kind = "unsolved_goals" if result.status == "incomplete" else "proof_error"
            elif proc["returncode"] != 0:
                result.status, result.detail = "process_error", "nonzero process exit without a Lean error diagnostic"
            elif result.axioms is not None and "sorryAx" in result.axioms:
                result.status = "incomplete"
                result.failure_kind = "sorry_dependency"
            elif result.axioms is None or unparsed:
                result.status = "process_error"
                result.detail = "missing axiom audit or unparsed compiler output"
            elif set(result.axioms) - set(t.config.get("allowed_axioms", ["propext", "Classical.choice", "Quot.sound"])):
                result.status, result.detail = "invalid_candidate", "unapproved transitive axioms"
                result.failure_kind = "unapproved_axioms"
            elif guard_rejected:
                result.status, result.detail = "invalid_candidate", "trusted input failed proof boundary/policy check"
                result.failure_kind = "policy"
            else:
                result.status, result.sorries = "candidate_pass", []
                measured = self._with_support(text[:t.declaration_start] + "#repair_measure\n" + text[t.declaration_start:])
                _, mp, mm, mu = self._run(measured + self._audit_suffix(), attempt + "_metrics", True,
                                         heartbeat_limit=heartbeat_limit)
                values = [int(m["message"].split("|", 1)[1]) for m in mm
                          if str(m["message"]).startswith("REPAIR_HEARTBEATS|")]
                if self._heartbeat_exceeded(mm):
                    result.status, result.detail = "resource_limit", "Lean maxHeartbeats exceeded during measurement"
                elif self._process_status(mp) or mp["returncode"] != 0 or mu or len(values) != 1:
                    result.status, result.detail = self._process_status(mp) or "process_error", "heartbeat measurement failed"
                else:
                    raw = values[0]
                    result.metrics.update(raw_heartbeats=raw, heartbeats=raw // 1000)
                    cap = t.limits.get("heartbeats") or t.limits["max_heartbeats"]
                    if check_kind != "reference" and raw > cap * 1000:
                        result.status, result.detail = "resource_limit", "measured heartbeat limit exceeded"
                    elif check_kind == "final":
                        result.status = "verified"
            if result.status in {"proof_error", "incomplete"}:
                result.goals, result.local_context, sorries = self._context(text, messages, attempt)
                result.sorries = sorries or None
                if result.axioms is not None and "sorryAx" in result.axioms:
                    result.sorries = (result.sorries or []) + [{"kind": "transitive_dependency", "axiom": "sorryAx",
                                                              "position": None, "end_position": None}]
            if self.reference_metrics:
                for name in ("proof_tokens", "heartbeats"):
                    before, after = self.reference_metrics.get(name), result.metrics.get(name)
                    result.metrics[name + "_reduction_pct"] = round(100 * (1 - after / before), 4) if before and after is not None else None
            t.assert_statement(text)
            if self._environment() != self.environment:
                result.status, result.detail = "environment_error", "environment changed during verification"
            if result.status == "verified":
                # Save exact uninstrumented bytes only after preservation checks.
                (self.out / "successful.lean").write_text(text)
            write_json(dest / "verification.json", result.to_dict())
            self.runner.trace.emit("verification", **result.to_dict())
            return result
        except StatementMismatch as exc:
            result.status, result.statement_check = "statement_mismatch", "mismatch"
            result.failure_kind, result.detail = "statement_mismatch", str(exc)
            return result
        except (OSError, ValueError, subprocess.SubprocessError) as exc:
            result.status, result.detail = "environment_error", str(exc)
            return result
