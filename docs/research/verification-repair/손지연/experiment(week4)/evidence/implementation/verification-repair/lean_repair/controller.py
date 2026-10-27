"""Sequential verify -> repair -> reverify, independent of Lean/model backends."""
import time

from .contracts import StatementMismatch, VerificationResult, digest, write_json
from .model import ModelError


REPAIRABLE = {"proof_error", "incomplete", "invalid_candidate", "resource_limit"}
TRANSIENT = {"timeout", "environment_error", "process_error"}
DEFINITIVE = REPAIRABLE | {"candidate_pass", "verified"}


class FinalVerifier:
    def __init__(self, backend):
        self.backend = backend

    def verify(self, body, label):
        return self.backend.verify(body, label, "final")


class Controller:
    def __init__(self, task, verifier, model, budget, trace, runner):
        self.task, self.verifier, self.model, self.budget = task, verifier, model, budget
        self.trace, self.runner = trace, runner
        self.final = FinalVerifier(verifier)

    def _verify(self, body, label, final=False):
        try:
            return self.final.verify(body, label) if final else self.verifier.verify(body, label)
        except StatementMismatch as exc:
            return VerificationResult(self.task.task_id, label, digest(body), "not_checked",
                                      "final" if final else "candidate", "statement_mismatch",
                                      statement_check="mismatch", failure_kind="statement_mismatch", detail=str(exc))

    def run(self, body=None):
        task = self.task
        result = {"task_id": task.task_id, "status": "stopped", "stop_reason": None,
                  "attempts": [], "model_configured": self.model is not None,
                  "api_budget_before": self.budget.snapshot(),
                  "metric_scope": "local Lean lexer proof tokens; target elaboration heartbeats; one pinned version"}
        cache, history = {}, []

        def finish(reason, status="stopped"):
            result.update(stop_reason=reason, status=status, api_budget=self.budget.snapshot())
            result["api_requests_this_run"] = result["api_budget"]["calls"] - result["api_budget_before"]["calls"]
            write_json(self.trace.directory / "result.json", result)
            self.trace.emit("stop", **result)
            return result

        try:
            prepared = self.verifier.prepare()
        except StatementMismatch as exc:
            result["detail"] = str(exc)
            return finish("statement_mismatch")
        self.trace.emit("prepare", **prepared.to_dict())
        if prepared.status == "statement_mismatch" or prepared.statement_check == "mismatch":
            result["final"] = prepared.to_dict()
            return finish("statement_mismatch")
        if prepared.status != "candidate_pass":
            return finish(prepared.status)
        # Setup has its own timeout. The experiment wall budget begins after environment preparation.
        self.runner.deadline = time.monotonic() + task.limits["task_seconds"]
        current = task.initial_body if body is None else body
        checked = None
        label = "initial"
        calls, format_error = 0, None
        for _ in range(task.limits["repair_calls"] + 1):
            if self.runner.remaining <= 0:
                return finish("wall_time_limit")
            key = digest(current)
            if key in cache:
                checked = cache[key]
                self.trace.emit("duplicate", candidate_hash=key, previous_status=checked.status)
                feedback = checked.to_dict() | {"detail": "already judged; propose a different body"}
            else:
                for retry in range(task.limits["infra_retries"] + 1):
                    checked = self._verify(current, label + (f"_infra{retry}" if retry else ""))
                    if checked.status == "statement_mismatch" or checked.statement_check == "mismatch" or checked.status not in TRANSIENT:
                        break
                    self.trace.emit("infrastructure_retry", retry=retry, **checked.to_dict())
                if checked.status in DEFINITIVE:
                    cache[key] = checked
                feedback = checked.to_dict()
                result["attempts"].append(feedback)
                self.trace.emit("candidate", **feedback)
                if checked.status == "statement_mismatch" or checked.statement_check == "mismatch":
                    result["final"] = feedback
                    return finish("statement_mismatch")
                if checked.status == "candidate_pass":
                    final = self._verify(current, label + "_final", final=True)
                    result["attempts"].append(final.to_dict())
                    self.trace.emit("final", **final.to_dict())
                    if final.status == "statement_mismatch" or final.statement_check == "mismatch":
                        result["final"] = final.to_dict()
                        return finish("statement_mismatch")
                    if final.status == "verified":
                        result["final"] = final.to_dict()
                        return finish("verified", "verified")
                    checked, feedback = final, final.to_dict()
                    # Final proof failures can be repaired while request/time budget remains.
                    if final.status in DEFINITIVE:
                        cache[key] = final
                    else:
                        cache.pop(key, None)
            if checked.status == "statement_mismatch" or checked.statement_check == "mismatch":
                result["final"] = feedback
                return finish("statement_mismatch")
            if checked.status not in REPAIRABLE and checked.status != "candidate_pass":
                return finish(checked.status)
            if self.model is None:
                result["final"] = feedback
                return finish("verification_only")
            if calls >= task.limits["repair_calls"]:
                return finish("repair_limit")
            if format_error:
                feedback = feedback | {"model_response_error": format_error}
                format_error = None
            request = {"task_id": task.task_id, "target": task.config["target"],
                       "current_file": task.assemble(current), "verification": feedback,
                       "previous_attempts": history, "remaining_repairs": task.limits["repair_calls"] - calls,
                       "budget": self.budget.snapshot(),
                       "constraints": ["Return exactly diagnosis and proof_body as JSON strings.",
                                       "Replace the complete by proof only; keep all imports/statements/assumptions/definitions fixed.",
                                       "Local have proofs are allowed. No sorry/admit/new axioms/metaprogramming/resource option changes."]}
            calls += 1
            label = f"attempt_{calls:02d}"
            dest = self.trace.directory / "model" / label
            self.trace.emit("model_request", attempt=calls, budget=self.budget.snapshot())
            try:
                proposal = self.model.propose(request, dest, min(task.limits["model_seconds"], self.runner.remaining), self.budget)
            except ModelError as exc:
                if exc.reason in {"invalid_model_output", "incomplete_model_output", "invalid_or_unavailable_model_response"} and not self.budget.snapshot()["accounting_uncertain"]:
                    format_error = exc.reason
                    self.trace.emit("model_format_rejected", reason=exc.reason, budget=self.budget.snapshot())
                    continue
                return finish(exc.reason)
            except Exception as exc:
                self.trace.emit("adapter_error", error=type(exc).__name__)
                return finish("model_error")
            if (not isinstance(proposal, dict) or set(proposal) != {"diagnosis", "proof_body"}
                    or not all(isinstance(v, str) for v in proposal.values())):
                return finish("invalid_model_response")
            history.append({"candidate_hash": key, "verification": feedback,
                            "diagnosis": proposal["diagnosis"]})
            current = proposal["proof_body"]
        return finish("repair_limit")
