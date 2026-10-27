"""HTTP is mocked: these tests never issue a paid or public network request."""
from copy import deepcopy
from decimal import Decimal
import io
import json
import os
from pathlib import Path
import signal
import tempfile
import unittest
from unittest.mock import patch
from urllib.error import HTTPError

from week4.lean_repair.model import ApiBudget, ModelError, OpenRouterModel, cost_decimal, _ApiDeadline, _wall_deadline


MODEL = "test/model-v1"
CATALOGUE = {"data": [{"id": MODEL, "canonical_slug": MODEL, "context_length": 1000,
    "architecture": {"input_modalities": ["text"], "output_modalities": ["text"]},
    "pricing": {"prompt": "0.001", "completion": "0.002", "request": "0.01", "image": "0"},
    "top_provider": {"max_completion_tokens": 100}}]}


def response(**changes):
    result = {"id": "generation-test", "model": MODEL, "provider": "test-provider",
              "usage": {"prompt_tokens": 10, "completion_tokens": 20, "total_tokens": 30,
                        "cost": 0.06, "prompt_tokens_details": {"cached_tokens": 8},
                        "completion_tokens_details": {"reasoning_tokens": 15}},
              "choices": [{"finish_reason": "stop", "message": {"content": json.dumps({
                  "diagnosis": "Use the right assumption.", "proof_body": "by\n  exact h"})}}]}
    result.update(changes)
    return result


def http(body):
    return io.BytesIO(body.encode() if isinstance(body, str) else json.dumps(body).encode())


class ModelTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        self.auth = patch.dict(os.environ, {"OPENROUTER_API_KEY": "secret-test-key"})
        self.auth.start()
        self.addCleanup(self.auth.stop)
        self.model = OpenRouterModel({"model": MODEL, "max_output_tokens": 100})

    def invoke(self, reply, budget=None, catalogue=None):
        budget = budget or ApiBudget()
        with patch("week4.lean_repair.model.urllib.request.urlopen", side_effect=[http(catalogue or CATALOGUE), http(reply)]) as mocked:
            proposal = self.model.propose({"candidate": "by exact wrong", "feedback": {"status": "proof_error"}}, self.path, 5, budget)
        return proposal, budget, mocked

    def test_native_tokens_and_full_public_list_cost(self):
        proposal, budget, mocked = self.invoke(response())
        self.assertEqual(proposal["proof_body"], "by\n  exact h")
        self.assertEqual(budget.snapshot()["model_tokens"], 30)
        self.assertEqual(Decimal(budget.snapshot()["spent_usd"]), Decimal(".06"))
        self.assertEqual(budget.snapshot()["reserved_usd"], "0")
        record = json.loads((self.path / "usage.json").read_text())
        # Cached input is priced fully; reasoning is already in completion.
        self.assertEqual(Decimal(record["public_list_cost_usd"]), Decimal(".06"))
        request = mocked.call_args_list[1].args[0]
        payload = json.loads(request.data)
        self.assertEqual(payload["max_tokens"], 100)
        self.assertEqual(payload["response_format"], {"type": "json_object"})
        self.assertEqual(payload["provider"]["max_price"], {"prompt": 1000.0, "completion": 2000.0, "request": .01})
        self.assertTrue(payload["provider"]["require_parameters"])
        self.assertNotIn("tools", payload)
        self.assertNotIn("secret-test-key", "".join(p.read_text() for p in self.path.iterdir()))

    def test_provider_cost_higher_than_list_is_conservatively_charged(self):
        reply = response()
        reply["usage"]["cost"] = "0.09"
        _, budget, _ = self.invoke(reply)
        self.assertEqual(Decimal(budget.snapshot()["spent_usd"]), Decimal(".09"))
        self.assertEqual(json.loads((self.path / "usage.json").read_text())["provider_reported_cost_usd"], "0.09")

    def test_reserved_before_dispatch_and_catalogue_is_cached(self):
        budget = ApiBudget()
        calls = []
        def dispatch(request, **kwargs):
            calls.append(request)
            if isinstance(request, str):
                return http(CATALOGUE)
            self.assertEqual(budget.calls, len(calls) - 1)
            self.assertEqual(Decimal(budget.snapshot()["reserved_usd"]), Decimal("1.21"))
            return http(response())
        with patch("week4.lean_repair.model.urllib.request.urlopen", side_effect=dispatch):
            self.model.propose({}, self.path / "one", 5, budget)
            self.model.propose({}, self.path / "two", 5, budget)
        self.assertEqual(len(calls), 3)
        self.assertEqual(budget.calls, 2)

    def test_reservation_denied_without_paid_request(self):
        budget = ApiBudget({"limit_usd": "1"})
        with patch("week4.lean_repair.model.urllib.request.urlopen", return_value=http(CATALOGUE)) as mocked:
            with self.assertRaisesRegex(ModelError, "reservation_exceeds_budget"):
                self.model.propose({}, self.path, 5, budget)
        self.assertEqual(mocked.call_count, 1)
        self.assertEqual(budget.calls, 0)

    def test_token_reservation_denied(self):
        budget = ApiBudget({"max_model_tokens": 1099})
        with patch("week4.lean_repair.model.urllib.request.urlopen", return_value=http(CATALOGUE)) as mocked:
            with self.assertRaisesRegex(ModelError, "token_reservation"):
                self.model.propose({}, self.path, 5, budget)
        self.assertEqual(mocked.call_count, 1)

    def test_bad_candidate_still_costs_a_call(self):
        for content in ("not JSON", '{"diagnosis":"x","proof_body":"by exact h","extra":"x"}', '{"diagnosis":"x","proof_body":""}'):
            with self.subTest(content=content):
                budget = ApiBudget()
                reply = response(choices=[{"finish_reason": "stop", "message": {"content": content}}])
                self.model.metadata = None
                with self.assertRaises(ModelError):
                    self.invoke(reply, budget)
                self.assertEqual(budget.calls, 1)
                self.assertEqual(Decimal(budget.snapshot()["spent_usd"]), Decimal(".06"))
                self.assertFalse(budget.uncertain)

    def test_unknown_errors_keep_reservation_and_stop_future_calls(self):
        for failure in (TimeoutError(), HTTPError("https://openrouter.ai/api/v1/chat/completions", 500, "secret-test-key", {}, None)):
            with self.subTest(failure=type(failure).__name__):
                model = OpenRouterModel({"model": MODEL, "max_output_tokens": 100})
                budget = ApiBudget()
                with patch("week4.lean_repair.model.urllib.request.urlopen", side_effect=[http(CATALOGUE), failure]) as mocked:
                    with self.assertRaises(ModelError):
                        model.propose({}, self.path / "failed", 5, budget)
                    with self.assertRaisesRegex(ModelError, "accounting_unknown"):
                        model.propose({}, self.path / "blocked", 5, budget)
                self.assertEqual(mocked.call_count, 2)
                self.assertEqual(budget.calls, 1)
                self.assertEqual(Decimal(budget.snapshot()["reserved_usd"]), Decimal("1.21"))
                self.assertTrue(budget.uncertain)
                self.assertNotIn("secret-test-key", (self.path / "failed" / "error.json").read_text())

    def test_missing_or_malformed_usage_is_never_zero(self):
        cases = [None, {}, {"prompt_tokens": 1, "completion_tokens": 1},
                 {"prompt_tokens": -1, "completion_tokens": 1, "cost": 0},
                 {"prompt_tokens": 1.5, "completion_tokens": 1, "cost": 0},
                 {"prompt_tokens": True, "completion_tokens": 1, "cost": 0},
                 {"prompt_tokens": 1, "completion_tokens": 1, "cost": "NaN"},
                 {"prompt_tokens": 1, "completion_tokens": 1, "cost": -1},
                 {"prompt_tokens": 1, "completion_tokens": 1, "cost": 0, "total_tokens": 99}]
        for usage in cases:
            with self.subTest(usage=usage):
                self.model.metadata = None
                budget = ApiBudget()
                with self.assertRaises(ModelError):
                    self.invoke(response(usage=usage), budget)
                self.assertTrue(budget.uncertain)
                self.assertEqual(budget.calls, 1)
                self.assertEqual(Decimal(budget.snapshot()["committed_usd"]), Decimal("1.21"))

    def test_raw_non_json_and_api_error_keep_reservation(self):
        for reply in ("bad JSON", {"error": {"message": "server failed"}}):
            with self.subTest(reply=reply):
                self.model.metadata = None
                budget = ApiBudget()
                with self.assertRaises(ModelError):
                    self.invoke(reply, budget)
                self.assertTrue(budget.uncertain)

    def test_maximum_three_calls_and_no_unreported_tokens(self):
        budget = ApiBudget()
        for _ in range(3):
            call = budget.reserve(Decimal(".1"), 20)
            budget.settle(call, Decimal(".05"), 10)
        with self.assertRaisesRegex(ModelError, "call_budget"):
            budget.reserve(Decimal(".1"), 20)
        for config in ({"max_calls": 4}, {"limit_usd": "3.01"}, {"max_calls": True}):
            with self.assertRaises(ModelError):
                ApiBudget(config)

    def test_unsupported_and_invalid_pricing_stops_before_completion(self):
        for changes in ({"image": ".1"}, {"prompt": "NaN"}, {"prompt": "0"}, {"prompt": {"tiers": []}}, {"internal_reasoning": ".1"}):
            with self.subTest(changes=changes):
                catalogue = deepcopy(CATALOGUE)
                catalogue["data"][0]["pricing"].update(changes)
                model = OpenRouterModel({"model": MODEL, "max_output_tokens": 100})
                with patch("week4.lean_repair.model.urllib.request.urlopen", return_value=http(catalogue)) as mocked:
                    with self.assertRaises(ModelError):
                        model.propose({}, self.path, 5, ApiBudget())
                self.assertEqual(mocked.call_count, 1)

    def test_api_credential_is_required_and_endpoints_are_fixed(self):
        with patch.dict(os.environ, {}, clear=True), patch("week4.lean_repair.model.urllib.request.urlopen") as mocked:
            with self.assertRaisesRegex(ModelError, "missing_openrouter"):
                self.model.propose({}, self.path, 5, ApiBudget())
            mocked.assert_not_called()
        with patch.dict(os.environ, {"OPENROUTER_API_KEY": "secret\nkey"}), \
             patch("week4.lean_repair.model.urllib.request.urlopen") as mocked:
            with self.assertRaisesRegex(ModelError, "invalid_openrouter_api_key"):
                self.model.propose({}, self.path, 5, ApiBudget())
            mocked.assert_not_called()
        for config in ({"model": "openrouter/auto"}, {"model": "test/model:free"},
                       {"model": MODEL, "api_base": "http://localhost:1234/api/v1"}):
            with self.assertRaises(ModelError):
                OpenRouterModel(config)

    def test_non_finite_costs_are_rejected(self):
        for value in ("NaN", "Infinity", "-1", True, None, {}):
            with self.assertRaises(ModelError):
                cost_decimal(value)

    def ledger_config(self, **changes):
        return {"ledger_path": str(self.path / "budget.json"), "task_id": "problem-17", **changes}

    def test_durable_ledger_keeps_cost_and_calls_across_runs(self):
        with ApiBudget(self.ledger_config()) as first:
            call = first.reserve(Decimal("1"), 100)
            first.settle(call, Decimal(".75"), 60)
        with ApiBudget(self.ledger_config()) as resumed:
            self.assertEqual(resumed.calls, 1)
            self.assertEqual(resumed.spent, Decimal(".75"))
            self.assertEqual(resumed.tokens, 60)
            self.assertFalse(resumed.uncertain)
            for _ in range(2):
                call = resumed.reserve(Decimal("1"), 100)
                resumed.settle(call, Decimal(".5"), 10)
            with self.assertRaisesRegex(ModelError, "call_budget"):
                resumed.reserve(Decimal(".1"), 10)

    def test_crash_reservation_survives_and_blocks_restart(self):
        first = ApiBudget(self.ledger_config())
        first.reserve(Decimal("1.21"), 1100)
        state = json.loads((self.path / "budget.json").read_text())
        self.assertEqual(state["entries"][0]["state"], "reserved")
        first.close()  # Simulate exit after dispatch, before its outcome is known.
        with ApiBudget(self.ledger_config()) as restarted:
            self.assertTrue(restarted.uncertain)
            self.assertEqual(Decimal(restarted.snapshot()["reserved_usd"]), Decimal("1.21"))
            with self.assertRaisesRegex(ModelError, "accounting_unknown"):
                restarted.reserve(Decimal(".1"), 10)

    def test_concurrent_ledger_users_are_excluded(self):
        with ApiBudget(self.ledger_config()):
            with self.assertRaisesRegex(ModelError, "ledger_locked"):
                ApiBudget(self.ledger_config())
        # Closing releases the lock so a later run can load the same ledger.
        with ApiBudget(self.ledger_config()) as later:
            self.assertEqual(later.calls, 0)

    def test_malformed_or_mismatched_ledger_cannot_reset_accounting(self):
        with ApiBudget(self.ledger_config()) as original:
            call = original.reserve(Decimal("1"), 100)
            original.settle(call, Decimal(".5"), 10)
        path = self.path / "budget.json"
        baseline = path.read_text()
        for text in ("not JSON", "{}", baseline.replace('"cost_usd": "0.5"', '"cost_usd": "NaN"'),
                     baseline.replace('"call": 1', '"call": 0'),
                     baseline.replace('"accounting_uncertain": false', '"accounting_uncertain": 0')):
            with self.subTest(text=text):
                path.write_text(text)
                with self.assertRaisesRegex(ModelError, "invalid_or_mismatched_api_ledger"):
                    ApiBudget(self.ledger_config())
        path.write_text(baseline)
        for changes in ({"task_id": "other-problem"}, {"limit_usd": "2"}, {"max_calls": 2}):
            with self.assertRaisesRegex(ModelError, "invalid_or_mismatched_api_ledger"):
                ApiBudget(self.ledger_config(**changes))

    def test_reservation_is_durable_before_network_dispatch(self):
        with ApiBudget(self.ledger_config()) as budget:
            def dispatch(request, **kwargs):
                if isinstance(request, str):
                    return http(CATALOGUE)
                state = json.loads((self.path / "budget.json").read_text())
                self.assertEqual(state["entries"][0]["state"], "reserved")
                self.assertEqual(Decimal(state["entries"][0]["reserved_usd"]), Decimal("1.21"))
                raise TimeoutError()
            with patch("week4.lean_repair.model.urllib.request.urlopen", side_effect=dispatch):
                with self.assertRaises(ModelError):
                    self.model.propose({}, self.path / "model", 5, budget)
        with ApiBudget(self.ledger_config()) as restarted:
            self.assertTrue(restarted.uncertain)
            self.assertEqual(restarted.calls, 1)

    def test_provider_overrun_keeps_actual_charge_and_blocks_new_calls(self):
        reply = response()
        reply["usage"]["cost"] = 1.5
        with ApiBudget(self.ledger_config()) as budget:
            with self.assertRaisesRegex(ModelError, "exceeds_reservation"):
                self.invoke(reply, budget)
            self.assertEqual(budget.spent, Decimal("1.5"))
        with ApiBudget(self.ledger_config()) as restarted:
            self.assertTrue(restarted.uncertain)
            self.assertEqual(restarted.spent, Decimal("1.5"))

    def test_wall_timeout_after_dispatch_keeps_reservation(self):
        budget = ApiBudget()
        def dispatch(request, **kwargs):
            if isinstance(request, str):
                return http(CATALOGUE)
            signal.raise_signal(signal.SIGALRM)
        with patch("week4.lean_repair.model.urllib.request.urlopen", side_effect=dispatch):
            with self.assertRaisesRegex(ModelError, "api_wall_timeout"):
                self.model.propose({}, self.path, 5, budget)
        self.assertEqual(budget.calls, 1)
        self.assertTrue(budget.uncertain)
        self.assertEqual(Decimal(budget.snapshot()["reserved_usd"]), Decimal("1.21"))

    def test_wall_timeout_before_dispatch_does_not_reserve(self):
        budget = ApiBudget()
        def dispatch(*args, **kwargs):
            signal.raise_signal(signal.SIGALRM)
        with patch("week4.lean_repair.model.urllib.request.urlopen", side_effect=dispatch):
            with self.assertRaisesRegex(ModelError, "api_timeout_before_dispatch"):
                self.model.propose({}, self.path, 5, budget)
        self.assertEqual(budget.calls, 0)
        self.assertEqual(budget.snapshot()["committed_usd"], "0")

    def test_prior_alarm_handler_and_remaining_timer_are_restored(self):
        previous = lambda *_: None
        with patch("week4.lean_repair.model.signal.getsignal", return_value=previous), \
             patch("week4.lean_repair.model.signal.getitimer", return_value=(10., 2.)), \
             patch("week4.lean_repair.model.signal.signal") as handlers, \
             patch("week4.lean_repair.model.signal.setitimer") as timers, \
             patch("week4.lean_repair.model.time.monotonic", side_effect=[100., 100.25]):
            with _wall_deadline(3):
                pass
        self.assertEqual(timers.call_args_list[0].args, (signal.ITIMER_REAL, 3))
        self.assertEqual(timers.call_args_list[-1].args, (signal.ITIMER_REAL, 9.75, 2.))
        self.assertEqual(handlers.call_args_list[-1].args, (signal.SIGALRM, previous))

    def test_existing_earlier_alarm_is_honored(self):
        previous = unittest.mock.Mock()
        with patch("week4.lean_repair.model.signal.getsignal", return_value=previous), \
             patch("week4.lean_repair.model.signal.getitimer", return_value=(1., 0.)), \
             patch("week4.lean_repair.model.signal.signal") as handlers, \
             patch("week4.lean_repair.model.signal.setitimer") as timers, \
             patch("week4.lean_repair.model.time.monotonic", side_effect=[100., 101.]):
            with self.assertRaises(_ApiDeadline):
                with _wall_deadline(3):
                    handlers.call_args_list[0].args[1](signal.SIGALRM, None)
        previous.assert_called_once_with(signal.SIGALRM, None)
        self.assertEqual(timers.call_args_list[0].args, (signal.ITIMER_REAL, 1.))
        self.assertEqual(timers.call_args_list[-1].args, (signal.ITIMER_REAL, 0))

    def test_background_thread_rejected_before_network(self):
        with patch("week4.lean_repair.model.threading.current_thread", return_value=object()), \
             patch("week4.lean_repair.model.urllib.request.urlopen") as mocked:
            with self.assertRaisesRegex(ModelError, "requires_posix_main_thread"):
                self.model.propose({}, self.path, 5, ApiBudget())
        mocked.assert_not_called()


if __name__ == "__main__":
    unittest.main()
