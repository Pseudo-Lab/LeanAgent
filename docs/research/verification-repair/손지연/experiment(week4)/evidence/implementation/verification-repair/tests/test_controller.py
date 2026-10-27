"""Controller contracts with fake backends; no Lean or model/network calls."""
from decimal import Decimal
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest

from week4.lean_repair.contracts import StatementMismatch, VerificationResult, digest
from week4.lean_repair.controller import Controller
from week4.lean_repair.model import ApiBudget, ModelError
from week4.lean_repair.runtime import ProcessRunner, Trace


class Backend:
    def __init__(self, statuses, prepared="candidate_pass"):
        self.statuses, self.calls = iter(statuses), []
        self.prepared = prepared
        self.results = []

    @staticmethod
    def result(status, attempt, candidate_hash="", check_kind="environment"):
        if isinstance(status, Exception):
            raise status
        if isinstance(status, VerificationResult):
            return status
        values = {"status": status} if isinstance(status, str) else status
        return VerificationResult("t", attempt, candidate_hash, "env", check_kind, **values)

    def prepare(self):
        return self.result(self.prepared, "prepare")

    def verify(self, body, attempt, check_kind="candidate"):
        self.calls.append((body, check_kind))
        result = self.result(next(self.statuses), attempt, digest(body), check_kind)
        self.results.append(result)
        return result


class Model:
    def __init__(self, proposals):
        self.proposals, self.requests = iter(proposals), []

    def propose(self, request, directory, timeout, budget):
        self.requests.append(request)
        call = budget.reserve(Decimal(".1"), 100)
        budget.settle(call, Decimal(".01"), 10)
        response = next(self.proposals)
        if isinstance(response, Exception):
            raise response
        if callable(response):
            response = response()
        return {"diagnosis": "fake response", "proof_body": response}


class ControllerTests(unittest.TestCase):
    def run_loop(self, statuses, proposals=None, prepared="candidate_pass"):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        trace = Trace(Path(temp.name) / "run")
        runner = ProcessRunner(trace, 30)
        task = SimpleNamespace(task_id="t", initial_body="by exact wrong", config={"target": "T"},
                               limits={"repair_calls": 3, "task_seconds": 30, "model_seconds": 2, "infra_retries": 1},
                               assemble=lambda body: "theorem T : True := " + body)
        backend = Backend(statuses, prepared)
        model = Model(proposals) if proposals is not None else None
        budget = ApiBudget()
        result = Controller(task, backend, model, budget, trace, runner).run()
        return result, backend, model

    def test_preparation_statement_mismatch_never_checks_or_repairs(self):
        for prepared in ("statement_mismatch", {"status": "candidate_pass", "statement_check": "mismatch"},
                         StatementMismatch("source statement changed before prepare")):
            with self.subTest(prepared=prepared):
                result, backend, model = self.run_loop([], [], prepared=prepared)
                self.assertEqual(result["stop_reason"], "statement_mismatch")
                self.assertEqual(result["status"], "stopped")
                self.assertEqual(backend.calls, [])
                self.assertEqual(model.requests, [])
                self.assertEqual(result["api_budget"]["calls"], 0)

    def test_candidate_statement_mismatch_is_fatal_even_with_pass_status(self):
        for candidate in ("statement_mismatch", {"status": "candidate_pass", "statement_check": "mismatch"},
                          {"status": "verified", "statement_check": "mismatch"},
                          StatementMismatch("source statement changed before candidate")):
            with self.subTest(candidate=candidate):
                result, backend, model = self.run_loop([candidate], [])
                self.assertEqual(result["stop_reason"], "statement_mismatch")
                self.assertEqual(result["status"], "stopped")
                self.assertEqual([kind for _, kind in backend.calls], ["candidate"])
                self.assertEqual(model.requests, [])
                self.assertEqual(result["api_budget"]["calls"], 0)

    def test_final_statement_mismatch_is_fatal_even_with_verified_status(self):
        for final in ("statement_mismatch", {"status": "verified", "statement_check": "mismatch"},
                      StatementMismatch("source statement changed before final")):
            with self.subTest(final=final):
                result, backend, model = self.run_loop(["candidate_pass", final], [])
                self.assertEqual(result["stop_reason"], "statement_mismatch")
                self.assertEqual(result["status"], "stopped")
                self.assertEqual([kind for _, kind in backend.calls], ["candidate", "final"])
                self.assertEqual(model.requests, [])
                self.assertEqual(result["api_budget"]["calls"], 0)

    def test_invalid_candidate_remains_repairable(self):
        result, _, model = self.run_loop(["invalid_candidate", "candidate_pass", "verified"], ["by trivial"])
        self.assertEqual(result["status"], "verified")
        self.assertEqual(model.requests[0]["verification"]["status"], "invalid_candidate")
        self.assertEqual(result["api_budget"]["calls"], 1)

    def test_repeated_invalid_candidates_stop_at_repair_limit(self):
        result, backend, model = self.run_loop(["invalid_candidate"] * 4,
                                               ["by bad one", "by bad two", "by bad three"])
        self.assertEqual(result["stop_reason"], "repair_limit")
        self.assertEqual(result["status"], "stopped")
        self.assertEqual(len(backend.calls), 4)
        self.assertEqual(len(model.requests), 3)

    def test_cached_statement_mismatch_is_not_sent_for_another_repair(self):
        cached = VerificationResult("t", "initial", digest("by exact wrong"), "env", "candidate", "proof_error")

        def flag_mismatch_then_repeat():
            cached.statement_check = "mismatch"
            return "by exact wrong"

        result, backend, model = self.run_loop([cached], [flag_mismatch_then_repeat])
        self.assertEqual(result["stop_reason"], "statement_mismatch")
        self.assertEqual(result["status"], "stopped")
        self.assertEqual(len(backend.calls), 1)
        self.assertEqual(len(model.requests), 1)

    def test_initial_valid_needs_fresh_final_and_no_model(self):
        result, backend, model = self.run_loop(["candidate_pass", "verified"], [])
        self.assertEqual(result["status"], "verified")
        self.assertEqual([kind for _, kind in backend.calls], ["candidate", "final"])
        self.assertEqual(model.requests, [])

    def test_error_then_success_uses_feedback_and_final(self):
        result, backend, model = self.run_loop(["proof_error", "candidate_pass", "verified"], ["by trivial"])
        self.assertEqual(result["status"], "verified")
        self.assertEqual(model.requests[0]["verification"]["status"], "proof_error")
        self.assertEqual(result["api_budget"]["calls"], 1)

    def test_final_proof_failure_returns_to_repair(self):
        result, _, model = self.run_loop(["proof_error", "candidate_pass", "proof_error", "candidate_pass", "verified"],
                                         ["by first", "by second"])
        self.assertEqual(result["status"], "verified")
        self.assertEqual(model.requests[1]["verification"]["check_kind"], "final")
        self.assertEqual(result["api_budget"]["calls"], 2)

    def test_duplicate_does_not_rerun_lean_but_still_costs(self):
        result, backend, _ = self.run_loop(["proof_error", "proof_error", "proof_error"],
                                           ["by one", "by one", "by two"])
        self.assertEqual(len(backend.calls), 3)
        self.assertEqual(result["stop_reason"], "repair_limit")
        self.assertEqual(result["api_budget"]["calls"], 3)

    def test_timeout_is_retried_without_new_model_call(self):
        result, backend, _ = self.run_loop(["proof_error", "timeout", "candidate_pass", "verified"], ["by trivial"])
        self.assertEqual(result["status"], "verified")
        self.assertEqual(backend.calls[1][0], backend.calls[2][0])
        self.assertEqual(result["api_budget"]["calls"], 1)

    def test_environment_failure_is_bounded_and_not_proof_failure(self):
        result, backend, model = self.run_loop(["environment_error", "environment_error"], [])
        self.assertEqual(result["stop_reason"], "environment_error")
        self.assertEqual(len(backend.calls), 2)
        self.assertFalse(model.requests)

    def test_known_cost_invalid_output_can_retry(self):
        result, _, model = self.run_loop(["proof_error", "candidate_pass", "verified"],
                                         [ModelError("invalid_model_output"), "by trivial"])
        self.assertEqual(result["status"], "verified")
        self.assertEqual(result["api_budget"]["calls"], 2)
        self.assertEqual(model.requests[1]["verification"]["model_response_error"], "invalid_model_output")

    def test_check_only_does_not_request_repair(self):
        result, _, _ = self.run_loop(["proof_error"])
        self.assertEqual(result["stop_reason"], "verification_only")
        self.assertEqual(result["api_budget"]["calls"], 0)
