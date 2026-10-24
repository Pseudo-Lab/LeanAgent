"""CLI startup failures retain a trace without touching models or API ledgers."""
from contextlib import redirect_stderr, redirect_stdout
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from week4.lean_repair import __main__ as cli
from week4.lean_repair.contracts import digest, write_json


class CliStartupTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.project = self.root / "project"
        self.project.mkdir()
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.33.0-rc2\n")
        self.text = "namespace N\ntheorem t : True := by\n  trivial\n\nend N\n"
        self.source = self.root / "input.lean"
        self.source.write_text(self.text)
        self.task_file = self.root / "task.json"
        self.run_index = 0
        self.config = {
            "task_id": "cli-startup-test",
            "source": "input.lean",
            "project": "project",
            "target": "N.t",
            "span": {"declaration_start": self.text.index("theorem t"),
                     "body_start": self.text.index("by\n"),
                     "body_end": self.text.index("\n\nend N")},
            "pins": {"source_sha256": digest(self.text),
                     "toolchain": "leanprover/lean4:v4.33.0-rc2"},
            "model": {"model": "unused-model"},
        }
        write_json(self.task_file, self.config)

    def startup_failure(self, command, expected_reason, message=None):
        self.run_index += 1
        out = self.root / f"{command}-run-{self.run_index}"
        stdout, stderr = io.StringIO(), io.StringIO()
        secret = "test-api-key-that-must-not-appear-in-startup-artifacts"
        with patch.dict(os.environ, {"OPENROUTER_API_KEY": secret}), \
                patch.object(cli, "ApiBudget") as budget, \
                patch.object(cli, "OpenRouterModel") as model, \
                patch.object(cli, "LeanVerifier") as verifier, \
                redirect_stdout(stdout), redirect_stderr(stderr):
            exit_code = cli.main([command, "--task", str(self.task_file), "--output", str(out)])
        self.assertEqual(exit_code, 2)
        budget.assert_not_called()
        model.assert_not_called()
        verifier.assert_not_called()
        self.assertTrue((out / "result.json").is_file())
        self.assertTrue((out / "trace.jsonl").is_file())
        result = json.loads((out / "result.json").read_text())
        events = [json.loads(line) for line in (out / "trace.jsonl").read_text().splitlines()]
        self.assertEqual(result["status"], "stopped")
        self.assertEqual(result["stop_reason"], expected_reason)
        self.assertIsNone(result["api_budget"])
        self.assertEqual(result["api_requests_this_run"], 0)
        self.assertIsInstance(result["detail"], str)
        self.assertTrue(result["detail"])
        if message:
            self.assertIn(message, result["detail"])
        self.assertEqual(events[-1]["event"], "stop")
        self.assertEqual(events[-1]["stop_reason"], expected_reason)
        artifact_text = "\n".join(p.read_text() for p in out.rglob("*") if p.is_file())
        self.assertNotIn(secret, artifact_text + stdout.getvalue() + stderr.getvalue())
        self.assertNotIn("Traceback (most recent call last)", artifact_text)
        return result

    def test_check_and_run_record_malformed_json_before_opening_a_budget(self):
        self.task_file.write_text("{invalid JSON")
        for command in ("check", "run"):
            with self.subTest(command=command):
                self.startup_failure(command, "config_error", "Expecting property name")

    def test_check_and_run_record_missing_input_without_a_model_call(self):
        self.source.unlink()
        for command in ("check", "run"):
            with self.subTest(command=command):
                self.startup_failure(command, "environment_error", "input.lean")

    def test_target_or_namespace_mismatch_stops_before_backend_setup(self):
        for command in ("check", "run"):
            with self.subTest(command=command):
                write_json(self.task_file, self.config | {"target": "Other.t"})
                self.startup_failure(command, "statement_mismatch", "target does not match")

    def test_invalid_limit_is_saved_as_configuration_error(self):
        write_json(self.task_file, self.config | {"limits": {"repair_calls": 4}})
        for command in ("check", "run"):
            with self.subTest(command=command):
                self.startup_failure(command, "config_error", "repair_calls")

    def test_malformed_configuration_shapes_are_recorded_as_configuration_errors(self):
        for config in ([], None, self.config | {"limits": None},
                       self.config | {"span": []}, self.config | {"pins": "invalid"}):
            for command in ("check", "run"):
                with self.subTest(config=config, command=command):
                    write_json(self.task_file, config)
                    self.startup_failure(command, "config_error")

    def test_missing_task_file_is_saved_as_environment_error(self):
        self.task_file.unlink()
        self.startup_failure("check", "environment_error", "task.json")


if __name__ == "__main__":
    unittest.main()
