"""Community REPL command/file/tactic adapter with the common result contract.

The REPL is an additional frontend observation. Proof boundaries, resource
measurement and axiom auditing use the CLI verifier; final acceptance always
uses a fresh CLI process on the assembled, uninstrumented file. In particular,
REPL tactic ``Completed`` never means that the original declaration was updated.
"""
import json
from pathlib import Path
import re
import shutil

from .contracts import StatementMismatch, VerificationResult, digest, write_json
from .lean import LeanVerifier


def _states(states):
    """Split pretty-printed proof states without confusing unknown with empty."""
    if states is None:
        return None, None
    goals, contexts = [], []
    for state in states:
        if not isinstance(state, str):
            continue
        for block in re.split(r"\n\s*\n", state):
            context, marker, goal = block.partition("⊢")
            if marker:
                goals.append(goal.strip())
                contexts.append(context.rstrip())
            elif block.strip():
                # An unfamiliar pretty-printer must never turn a nonempty goal
                # into an observed empty goal list.
                goals.append(block.strip())
                contexts.append("")
    return goals, contexts


def _position_valid(position):
    return position is None or (isinstance(position, dict)
                               and type(position.get("line")) is int and position["line"] >= 1
                               and type(position.get("column")) is int and position["column"] >= 0)


def _handle_valid(handle):
    return type(handle) is int and handle >= 0


def _records_valid(response):
    """Validate nested JSON before any field participates in sorting or hashing."""
    messages, tactics, sorries = (response.get(key, []) for key in ("messages", "tactics", "sorries"))
    if not all(isinstance(records, list) for records in (messages, tactics, sorries)):
        return False
    for record in messages:
        if (not isinstance(record, dict) or not isinstance(record.get("severity"), str)
                or record["severity"] not in {"info", "information", "trace", "warning", "error"}
                or not isinstance(record.get("data"), str)
                or not all(_position_valid(record.get(key)) for key in ("pos", "endPos"))):
            return False
    for record in tactics:
        if (not isinstance(record, dict) or not isinstance(record.get("tactic"), str)
                or not isinstance(record.get("goals"), str)
                or not all(_position_valid(record.get(key)) for key in ("pos", "endPos"))
                or (record.get("proofState") is not None and not _handle_valid(record["proofState"]))):
            return False
    for record in sorries:
        if (not isinstance(record, dict)
                or (record.get("goal") is not None and not isinstance(record["goal"], str))
                or not all(_position_valid(record.get(key)) for key in ("pos", "endPos"))
                or (record.get("proofState") is not None and not _handle_valid(record["proofState"]))):
            return False
    return True


def normalize_response(response, *, task_id="repl", attempt="request", candidate_hash="",
                       environment_id="not_checked", check_kind="candidate", process=None,
                       source_text=None, position_mapper=None):
    """Normalize a genuine command/file or tactic response, never final-accept it.

    Missing ``goals`` is unknown (None). An explicit empty list is observed empty.
    Top-level ``message`` is the REPL's Error variant, not a successful response.
    """
    result = VerificationResult(task_id, attempt, candidate_hash, environment_id,
                                check_kind, "process_error")
    map_position = position_mapper or (lambda position: position)
    if process:
        result.process_exit_code = process.get("returncode")
        result.elapsed_ms = process.get("elapsed_ms", 0)
        result.raw_log_path = process.get("stdout")
        failure = LeanVerifier._process_status(process)
        if failure:
            result.status, result.detail = failure, "REPL process failed before a complete response"
            return result
        if process.get("returncode") != 0:
            result.detail = "REPL process returned a nonzero exit code"
            return result
    if not isinstance(response, dict):
        result.detail = "REPL response must be a JSON object"
        return result
    if "message" in response:
        if not isinstance(response["message"], str):
            result.detail = "malformed REPL error message"
            return result
        message = response["message"]
        # Invalid session handles and transport errors are infrastructure failures.
        result.diagnostics = [{"severity": "error", "position": None, "end_position": None,
                               "message": message, "source": "lean_repl", "raw": response}]
        from .diagnostics import classify_error_status
        stripped = [{**result.diagnostics[0], "message": message.removeprefix("Lean error:").lstrip()}]
        if LeanVerifier._heartbeat_exceeded(stripped):
            result.status, result.detail = "resource_limit", "REPL maxHeartbeats exceeded"
        else:
            result.status = classify_error_status(stripped) if message.startswith("Lean error:") else "process_error"
        return result
    if not (_handle_valid(response.get("env")) or _handle_valid(response.get("proofState"))):
        result.detail = "REPL response lacks an environment or proof-state handle"
        return result
    if any(key in response and not _handle_valid(response[key]) for key in ("env", "proofState")):
        result.detail = "malformed REPL environment or proof-state handle"
        return result
    if not _records_valid(response):
        result.detail = "malformed REPL diagnostic, tactic or sorry record"
        return result
    for raw in response.get("messages", []):
        if not isinstance(raw, dict):
            result.detail = "malformed REPL diagnostic"
            return result
        result.diagnostics.append({"severity": "information" if raw.get("severity") == "info" else raw.get("severity"),
                                   "position": map_position(raw.get("pos")), "end_position": map_position(raw.get("endPos")),
                                   "message": raw.get("data"), "source": "lean_repl", "raw": raw})
    result.backend_proof_status = response.get("proofStatus")
    if result.backend_proof_status is not None and not isinstance(result.backend_proof_status, str):
        result.detail = "malformed REPL proofStatus"
        return result
    result.sorries = response.get("sorries", [])
    if not isinstance(result.sorries, list):
        result.detail = "malformed REPL sorries"
        return result
    if position_mapper:
        result.sorries = [{**s, "pos": map_position(s.get("pos")), "endPos": map_position(s.get("endPos")), "raw": s}
                          if isinstance(s, dict) else s for s in result.sorries]
    if "goals" in response:
        if not isinstance(response["goals"], list) or not all(isinstance(x, str) and x.strip() for x in response["goals"]):
            result.detail = "malformed REPL goal list"
            return result
        result.goals, result.local_context = _states(response["goals"])
    elif result.sorries:
        states = [s["goal"] for s in result.sorries if isinstance(s, dict) and isinstance(s.get("goal"), str) and s["goal"].strip()]
        if states:
            result.goals, result.local_context = _states(states)
    # allTactics provides actual syntax ranges and pre-tactic states. Pick the
    # narrowest enclosing tactic, rather than guessing from a list of tactic names.
    for diagnostic in result.diagnostics:
        if diagnostic["severity"] != "error":
            continue
        pos = diagnostic.get("position") or {}
        point = (pos.get("line", -1), pos.get("column", -1))
        matches = []
        for tactic in response.get("tactics", []):
            if not isinstance(tactic, dict):
                continue
            start, end = map_position(tactic.get("pos")) or {}, map_position(tactic.get("endPos")) or {}
            a = (start.get("line", -1), start.get("column", -1))
            b = (end.get("line", -1), end.get("column", -1))
            if a <= point < b:
                matches.append((a, b, tactic))
        if matches:
            # Later start and earlier end are nested more deeply.
            tactic = max(matches, key=lambda entry: (entry[0], (-entry[1][0], -entry[1][1])))[2]
            diagnostic["failed_tactic"] = tactic.get("tactic")
            diagnostic["tactic_position"] = map_position(tactic.get("pos"))
            diagnostic["tactic_end_position"] = map_position(tactic.get("endPos"))
            goals, contexts = _states([tactic.get("goals", "")])
            if goals:
                diagnostic["goals"], diagnostic["local_context"] = goals, contexts
                result.goals, result.local_context = goals, contexts
    if source_text is not None:
        from .diagnostics import enrich_diagnostics
        enrich_diagnostics(result.diagnostics, source_text)
    from .diagnostics import classify_error_status
    failure = classify_error_status(result.diagnostics)
    if LeanVerifier._heartbeat_exceeded(result.diagnostics):
        result.status, result.detail = "resource_limit", "REPL maxHeartbeats exceeded"
    elif failure:
        result.status = failure
    elif result.sorries or (result.backend_proof_status and result.backend_proof_status != "Completed"):
        result.status = "incomplete"
    elif result.goals:
        result.status = "incomplete"
    else:
        result.status = "candidate_pass"
    return result


class ReplClient:
    """Budgeted local JSON protocol client, with replayable command/tactic handles.

    Each query starts a fresh child and replays this client's prior requests.
    This keeps a single existing ProcessRunner responsible for timeout/process
    groups/logs, and keeps numeric handles valid within the deterministic history.
    History must not contain time-dependent or mutating Lean commands. The repair
    backend itself creates a new client for each complete-file observation.
    """
    def __init__(self, command, runner, project, directory, timeout):
        if not isinstance(command, list) or not command or not all(isinstance(x, str) and x for x in command):
            raise ValueError("REPL command must be a nonempty argv list")
        self.command, self.runner, self.project = command, runner, Path(project)
        self.directory, self.timeout = Path(directory), timeout
        self.history, self.responses = [], []

    def query(self, request):
        if not isinstance(request, dict) or sum(key in request for key in ("cmd", "path", "tactic")) != 1:
            raise ValueError("REPL request needs exactly one of cmd, path, tactic")
        dest = self.directory / f"request_{len(self.history) + 1:03d}"
        payloads = self.history + [request]
        stdin = "\n\n".join(json.dumps(p, ensure_ascii=False) for p in payloads) + "\n\n"
        proc = self.runner.run(self.command, self.project, dest, self.timeout, stdin=stdin)
        raw = Path(proc["stdout"]).read_text(errors="replace")
        decoded, offset, decoder = [], 0, json.JSONDecoder()
        try:
            while raw[offset:].strip():
                offset += len(raw[offset:]) - len(raw[offset:].lstrip())
                response, offset = decoder.raw_decode(raw, offset)
                if not isinstance(response, dict):
                    raise ValueError("non-object REPL response")
                decoded.append(response)
            if len(decoded) != len(payloads):
                raise ValueError("REPL response count differs from request count")
            if decoded[:-1] != self.responses:
                raise ValueError("REPL replay changed prior responses; session handles are unsafe")
        except ValueError as exc:
            proc["process_error"] = str(exc)
            write_json(dest / "protocol_error.json", {"error": str(exc)})
            self.runner.trace.emit("repl_protocol_error", error=str(exc), raw_log_path=proc["stdout"])
            return None, proc
        self.history.append(request)
        self.responses = decoded
        write_json(dest / "response.json", decoded[-1])
        return decoded[-1], proc

    def verify_request(self, request, **identity):
        response, proc = self.query(request)
        return normalize_response(response, process=proc, **identity)


class ReplVerifier(LeanVerifier):
    """REPL frontend with CLI boundary, axiom, measurement and final checks."""
    def __init__(self, task, runner):
        super().__init__(task, runner)
        backend = task.config.get("backend", {})
        command = backend.get("command")
        if not isinstance(command, list) or not command or not all(isinstance(x, str) and x for x in command):
            raise ValueError("backend.command must be a nonempty argv list for the community REPL")
        self.repl_command = ["elan", "run", task.config["pins"]["toolchain"], "lake", "env", *command]
        self.mode = backend.get("mode", "file")
        if not isinstance(self.mode, str) or self.mode not in {"file", "command"}:
            raise ValueError("REPL mode must be file or command")

    def _environment(self):
        snapshot = super()._environment()
        command = self.task.config["backend"]["command"]
        executable = shutil.which(command[0]) if "/" not in command[0] else command[0]
        executable = Path(executable) if executable else self.task.project / command[0]
        if not executable.is_absolute():
            executable = self.task.project / executable
        if not executable.is_file():
            raise ValueError("community REPL executable is unavailable")
        snapshot["repl"] = {"command": command, "mode": self.mode,
                            "executable": str(executable.resolve()),
                            "executable_sha256": digest(executable.read_bytes())}
        return snapshot

    def prepare(self):
        prepared = super().prepare()
        if prepared.status != "candidate_pass":
            return prepared
        try:
            self.task.assert_statement()
        except StatementMismatch as exc:
            prepared.status, prepared.statement_check = "statement_mismatch", "mismatch"
            prepared.failure_kind, prepared.detail = "statement_mismatch", str(exc)
            return prepared
        except OSError as exc:
            prepared.status, prepared.detail = "environment_error", str(exc)
            return prepared
        dest = self._directory("repl_environment")
        client = ReplClient(self.repl_command, self.runner, self.task.project, dest,
                            self.task.limits["lean_seconds"])
        observed = client.verify_request({"cmd": "import Lean\n#eval Lean.versionString"},
                                         task_id=self.task.task_id, attempt="prepare_repl",
                                         environment_id=self.environment_id, check_kind="environment")
        try:
            self.task.assert_statement()
        except StatementMismatch as exc:
            observed.status, observed.statement_check = "statement_mismatch", "mismatch"
            observed.failure_kind, observed.detail = "statement_mismatch", str(exc)
            write_json(dest / "verification.json", observed.to_dict())
            return observed
        except OSError as exc:
            observed.status, observed.detail = "environment_error", str(exc)
            write_json(dest / "verification.json", observed.to_dict())
            return observed
        expected = self.task.config["pins"]["toolchain"].rsplit(":", 1)[-1].removeprefix("v")
        versions = []
        for diagnostic in observed.diagnostics:
            if diagnostic["severity"] != "information":
                continue
            try:
                versions.append(json.loads(diagnostic["message"]))
            except (ValueError, TypeError):
                pass
        if observed.status != "candidate_pass" or versions != [expected]:
            observed.status = observed.status if observed.status in {"wall_time_limit", "timeout", "process_error"} else "environment_error"
            observed.detail = f"community REPL toolchain probe failed: expected {expected}, observed {versions}"
            write_json(dest / "verification.json", observed.to_dict())
            return observed
        write_json(dest / "version.json", {"expected": expected, "observed": versions[0],
                                           "raw_log_path": observed.raw_log_path})
        return prepared

    def verify(self, body, attempt, check_kind="candidate"):
        # Fresh CLI verification is deliberately authoritative for final acceptance.
        checked = super().verify(body, attempt, check_kind)
        if check_kind == "final" or checked.status not in {"candidate_pass", "proof_error", "incomplete"}:
            return checked
        text = self.task.assemble(body)
        dest = self._directory(attempt + "_repl")
        source = dest / "candidate.lean"
        from .diagnostics import source_header_end
        at = source_header_end(text[:self.task.declaration_start])
        cap = 0 if check_kind == "reference" else self.task.limits["max_heartbeats"]
        instrumented = text[:at] + f"set_option maxHeartbeats {cap}\n" + text[at:]
        inserted_line = text[:at].count("\n") + 1

        def original_position(position):
            if not isinstance(position, dict):
                return position
            line = position.get("line")
            if type(line) is int and line > inserted_line:
                return {**position, "line": line - 1}
            return position

        source.write_text(instrumented)
        client = ReplClient(self.repl_command, self.runner, self.task.project, dest,
                            self.task.limits["lean_seconds"])
        request = {"allTactics": True}
        request.update({"path": str(source)} if self.mode == "file" else {"cmd": instrumented})
        repl = client.verify_request(request, task_id=self.task.task_id, attempt=attempt,
                                     candidate_hash=digest(text), environment_id=self.environment_id,
                                     check_kind=check_kind, source_text=text, position_mapper=original_position)
        # Neither frontend can hide the other's failure. A successful REPL response
        # cannot clear a transitive sorryAx or a failed full-file CLI check.
        if repl.status != "candidate_pass" and not (checked.status == "proof_error" and repl.status == "incomplete"):
            checked.status, checked.detail = repl.status, repl.detail
        keys = {(d.get("severity"), d.get("message")) for d in repl.diagnostics}
        checked.diagnostics = repl.diagnostics + [d for d in checked.diagnostics
                                                 if (d.get("severity"), d.get("message")) not in keys]
        checked.backend_proof_status = repl.backend_proof_status
        if repl.goals is not None:
            checked.goals, checked.local_context = repl.goals, repl.local_context
        if repl.sorries:
            checked.sorries = (checked.sorries or []) + repl.sorries
        checked.metrics["repl_elapsed_ms"] = repl.elapsed_ms
        checked.elapsed_ms += repl.elapsed_ms
        checked.raw_log_path = repl.raw_log_path
        try:
            self.task.assert_statement()
            if self._environment() != self.environment:
                checked.status, checked.detail = "environment_error", "environment changed during REPL verification"
        except StatementMismatch as exc:
            checked.status, checked.statement_check = "statement_mismatch", "mismatch"
            checked.failure_kind, checked.detail = "statement_mismatch", str(exc)
        except (OSError, ValueError) as exc:
            checked.status, checked.detail = "environment_error", str(exc)
        write_json(dest / "verification.json", checked.to_dict())
        self.runner.trace.emit("repl_verification", **checked.to_dict())
        return checked
