"""Pure Python structural-pilot tests; no Lean process or checkout mutation."""
import importlib.util
from pathlib import Path
from types import SimpleNamespace
import unittest

PATH = Path(__file__).resolve().parents[1] / "structural-strategies-2026-10-22/run_pilot.py"
spec = importlib.util.spec_from_file_location("structural_pilot", PATH)
pilot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pilot)


class PilotTests(unittest.TestCase):
    def test_transformations_preserve_statement_and_single_target(self):
        for number, strategy in ((11, "S1"), (12, "S1"), (11, "S2"), (11, "S3")):
            row = pilot.runner.problem(number)
            candidate = pilot.transform(number, strategy, row["src"])
            self.assertNotEqual(candidate, row["src"])
            self.assertEqual(pilot.runner.validate_candidate(candidate, row["statement"]), [])
            if strategy == "S1" and number == 11:
                self.assertNotIn("set P₀_coeffs", candidate)
                self.assertIn("set P₁_coeffs", candidate)
            if strategy == "S3":
                self.assertEqual(candidate.count("have h2 := h_shared_pow"), 2)
                self.assertEqual(candidate.count("have h1 :"), row["src"].count("have h1 :"))

    def test_nonlegacy_output_must_be_isolated(self):
        with self.assertRaisesRegex(ValueError, "isolated"):
            pilot.runner.evaluate(SimpleNamespace(problem=12))

    def test_unsupported_problem(self):
        with self.assertRaises(ValueError):
            pilot.runner.problem(7)

    def result(self, **overrides):
        return {"problem": 11, "name": "demo", "version": "v1", "revision": "abc",
                "source_sha256": "src", "reference_sha256": "ref", "candidate_sha256": "ref",
                "status": "passed", "axioms": [], "heartbeat": 100, "proof_tokens": 10, **overrides}

    def test_axiom_free_improvement(self):
        result = pilot.compare(self.result(), self.result(heartbeat=90, proof_tokens=12))
        self.assertTrue(result["improved"])
        self.assertEqual(result["token_delta"], 2)

    def test_rejections(self):
        for change, expected in (({"axioms": ["Classical.choice"]}, "new_axioms"),
                                 ({"axioms": None}, "axioms_missing"),
                                 ({"heartbeat": None}, "measurement_failed"),
                                 ({"revision": "other"}, "environment_mismatch"),
                                 ({"status": "failed"}, "failed")):
            with self.subTest(change=change):
                result = pilot.compare(self.result(), self.result(**change))
                self.assertEqual(result["status"], expected)
                self.assertFalse(result["improved"])

    def test_failed_or_nonreference_baseline(self):
        for change in ({"status": "failed"}, {"candidate_sha256": "not-original"}):
            self.assertEqual(pilot.compare(self.result(**change), self.result())["status"], "baseline_unavailable")

    def test_equal_and_worse_not_improvements(self):
        for hb in (100, 110):
            self.assertFalse(pilot.compare(self.result(), self.result(heartbeat=hb))["improved"])


if __name__ == "__main__":
    unittest.main()
