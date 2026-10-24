import unittest

from week4.lean_repair.diagnostics import (apply_info_feedback, classify_error_status,
                                         enrich_diagnostics, map_info_records, split_states)


class DiagnosticsTests(unittest.TestCase):
    def test_open_goals_do_not_hide_real_errors(self):
        open_goal = {"severity": "error", "message": "unsolved goals\nh : P\n⊢ Q"}
        mismatch = {"severity": "error", "message": "Type mismatch"}
        self.assertEqual(classify_error_status([open_goal]), "incomplete")
        self.assertEqual(classify_error_status([open_goal, mismatch]), "proof_error")
        self.assertIsNone(classify_error_status([{"severity": "warning", "message": "declaration uses sorry"}]))

    def test_unicode_ranges_and_nested_tactic_selection(self):
        text = "-- α\nby\n  · exact h₁\n"
        message = {"severity": "error", "position": {"line": 3, "column": 10},
                   "end_position": {"line": 3, "column": 12}, "message": "unknown identifier"}
        enrich_diagnostics([message], text)
        self.assertEqual(message["source_text"], "h₁")
        start = len(text[:text.index("exact")].encode())
        end = len(text[:text.index("h₁") + 2].encode())
        records = map_info_records([
            {"kind": "tactic", "start": 50 + len("-- α\n".encode()), "end": 50 + end,
             "goals_before": ["⊢ outer"], "depth": 1},
            {"kind": "tactic", "start": 50 + start, "end": 50 + end,
             "goals_before": ["h₁ : P\n⊢ Q"], "depth": 2}], text, 50)
        goals, context, sorries = apply_info_feedback([message], records)
        self.assertEqual(goals, ["Q"])
        self.assertEqual(context, ["h₁ : P"])
        self.assertEqual(message["failed_tactic"], "exact h₁")
        self.assertEqual(sorries, [])

    def test_unavailable_state_remains_unknown(self):
        message = {"severity": "error", "message": "parse error", "start_byte_offset": 2}
        goals, contexts, _ = apply_info_feedback([message], [])
        self.assertIsNone(goals)
        self.assertIsNone(contexts)
        self.assertIn("context_unavailable_reason", message)
        self.assertEqual(split_states(["case left\nh : P\n⊢ Q\n\ncase right\nh : P\n⊢ R"]),
                         (["Q", "R"], ["case left\nh : P", "case right\nh : P"]))


if __name__ == "__main__":
    unittest.main()
