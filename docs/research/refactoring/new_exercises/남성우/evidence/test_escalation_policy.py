"""Synthetic policy contract tests; no Lean results or score claims."""
import copy
import unittest
from escalation_policy import decide, digest


def request():
    x = {
        "problem_id": "synthetic-routing-example", "status": "invalid",
        "baseline_verified": True,
        "environment": {"note": "synthetic routing fixture; no Lean run"},
        "statement": "example (P Q : Prop) (h : P ∨ Q) : Q ∨ P",
        "context": "import Lean",
        "original_proof": "by cases h with\n  | inl hp => exact Or.inr hp\n  | inr hq => exact Or.inl hq",
        "candidate_proof": "by\n  left\n  assumption",
        "candidate_hash": "fixture-only-not-an-actual-hash",
        "diagnostics": [{"kind": "synthetic", "message": "assumption cannot close selected goal"}],
        "localization": {"scope": "block", "trusted_pre_state": False,
                         "reason": "No actual goal-state capture in this fixture"},
        "local": {"state": "not_applicable", "evidence": [
            "Synthetic routing input, not a claim that actual aesop would fail"]},
        "llm_history": [],
        "budget": {"cap_usd": 3, "spent_usd": 0.5, "reserved_usd": 0,
                   "next_call_upper_bound_usd": 0.3},
        "constraints": ["Body only", "No sorry/admit/new axioms"],
        "gold_repair": "SECRET_GOLD_MUST_NOT_LEAK",
    }
    prefix = x["context"] + "\n" + x["statement"] + " := "
    x["source_contract"] = {
        "original_source": prefix + x["original_proof"] + "\n",
        "candidate_source": prefix + x["candidate_proof"] + "\n",
        "body_start": len(prefix), "body_end": len(prefix + x["original_proof"])}
    x["candidate_hash"] = digest(x["candidate_proof"])
    x["environment_hash"] = "synthetic-env"
    return x


def certificate(x):
    return {"candidate_hash": digest(x["candidate_proof"]), "environment_hash": x["environment_hash"],
            "capture": "before_failed_tactic", "prefix_replayed": True, "prefix_error_count": 0,
            "recovery_used": False, "contains_sorry": False,
            "state_digest": "synthetic-state", "replayed_state_digest": "synthetic-state"}


class PolicyTests(unittest.TestCase):
    def test_prompt_preview_does_not_authorize_or_invent_price(self):
        x = request()
        x['preview_only'] = True
        del x['budget']
        out = decide(x)
        self.assertEqual(out['action'], 'EMIT_LLM_PROMPT')
        self.assertFalse(out['budget_checked'])
        self.assertFalse(out['call_authorized'])
        self.assertIsNone(out['estimated_upper_bound_usd'])

    def test_environment_and_baseline_never_escalate(self):
        x = request()
        x.update(status="environment_error")
        self.assertEqual(decide(x)["action"], "FIX_ENVIRONMENT")
        x.update(status="invalid", baseline_verified=False)
        self.assertEqual(decide(x)["action"], "VERIFY_BASELINE")

    def test_local_pending_and_duplicate(self):
        x = request()
        x["local"]["state"] = "pending"
        self.assertEqual(decide(x)["action"], "RUN_LOCAL")
        x["duplicate_request"] = True
        self.assertEqual(decide(x)["action"], "REUSE_OR_STOP")

    def test_prompt_is_offline_and_gold_not_leaked(self):
        out = decide(request())
        self.assertEqual(out["action"], "EMIT_LLM_PROMPT")
        self.assertEqual(out["scope"], "body")
        self.assertFalse(out["api_called"])
        self.assertNotIn("SECRET_GOLD", out["prompt"])
        self.assertIn("original_proof", out["prompt"])

    def test_budget_accounts_for_reservation_and_unknown_price(self):
        x = request()
        x["budget"]["reserved_usd"] = 2.5
        self.assertEqual(decide(x)["action"], "SELECT_BEST")
        for value in [None, float("nan"), -1, True]:
            x["budget"]["next_call_upper_bound_usd"] = value
            self.assertEqual(decide(x)["action"], "PRICE_REQUEST")

    def test_same_failure_widens_scope_and_limit_stops(self):
        x = request()
        x["localization"] = {"scope": "tactic", "trusted_pre_state": True}
        x["state_certificate"] = certificate(x)
        x["llm_history"] = [{"mode": "repair", "scope": "tactic", "same_failure": True}]
        self.assertEqual(decide(x)["scope"], "block")
        x["llm_history"].append({"mode": "repair", "scope": "block", "same_failure": True})
        self.assertEqual(decide(x)["action"], "SELECT_BEST")

    def test_optimization_requires_measurement_and_opportunity(self):
        x = request()
        x["status"] = "valid"
        self.assertEqual(decide(x)["action"], "MEASURE")
        x["metrics_complete"] = True
        self.assertEqual(decide(x)["action"], "MEASURE")
        x["metrics"] = {"baseline_tokens": 100, "baseline_heartbeats": 100,
                        "candidate_tokens": 50, "candidate_heartbeats": 50,
                        "versions_passed": 1, "versions_total": 1,
                        "incumbent_score": 100/3, "all_versions_checked": True,
                        "candidate_hash": x["candidate_hash"], "environment_hash": x["environment_hash"],
                        "comparable_to_incumbent": True}
        self.assertEqual(decide(x)["action"], "SELECT_BEST")
        x["metrics"]["candidate_heartbeats"] = 125
        self.assertEqual(decide(x)["mode"], "optimization")
        y = copy.deepcopy(x)
        y["contract_violation"] = True
        self.assertEqual(decide(y)["action"], "REJECT_CANDIDATE")

    def test_statement_and_answer_changes_are_rejected(self):
        x = request()
        x["source_contract"]["candidate_source"] = x["source_contract"]["candidate_source"].replace(
            ": Q ∨ P :=", ": P ∨ Q :=")
        self.assertEqual(decide(x)["action"], "REJECT_CANDIDATE")
        x = request()
        del x["source_contract"]
        self.assertEqual(decide(x)["action"], "CHECK_CONTRACT")

    def test_boolean_trust_and_stale_certificate_do_not_localize(self):
        x = request()
        x["localization"] = {"scope": "tactic", "trusted_pre_state": True}
        self.assertEqual(decide(x)["scope"], "body")
        x["state_certificate"] = certificate(x)
        self.assertEqual(decide(x)["scope"], "tactic")
        for key, bad in [("candidate_hash", "stale"), ("recovery_used", True),
                         ("replayed_state_digest", "different"), ("prefix_error_count", 1)]:
            y = copy.deepcopy(x)
            y["state_certificate"][key] = bad
            self.assertEqual(decide(y)["scope"], "body")


if __name__ == "__main__":
    unittest.main()
