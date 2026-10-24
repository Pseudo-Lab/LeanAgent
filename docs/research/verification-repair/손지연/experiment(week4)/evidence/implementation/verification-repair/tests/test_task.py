"""Registration pins and boundary checks, with no Lean/model execution."""
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import tempfile
import unittest
from types import SimpleNamespace

from week4.lean_repair.__main__ import initialize
from week4.lean_repair.contracts import EnvironmentMismatch, StatementMismatch, TaskSpec, write_json


class TaskTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.project = self.root / "project"
        self.project.mkdir()
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.33.0-rc2\n")
        self.source = self.root / "Problem.lean"
        self.original = "namespace N\ntheorem t : True := by\n  exact True.intro\n\nend N\n"
        self.source.write_text(self.original)
        self.args = SimpleNamespace(source=self.source, project=self.project, target="N.t", task_id="problem-t",
                                    declaration_marker="theorem t", body_start_marker=":= by", body_end_marker="end N",
                                    output=self.root / "task.json", reference=None)

    def register(self):
        with redirect_stdout(io.StringIO()):
            initialize(self.args)
        return TaskSpec.load(self.args.output)

    def test_candidate_without_final_newline_preserves_command_boundary(self):
        task = self.register()
        self.assertEqual(task.assemble("by trivial"), "namespace N\ntheorem t : True := by trivial\n\nend N\n")
        self.assertEqual(self.source.read_text(), self.original)

    def test_ambiguous_end_marker_creates_no_configuration(self):
        self.source.write_text(self.original + "-- end N\n")
        with self.assertRaisesRegex(ValueError, "exactly once"):
            self.register()
        self.assertFalse(self.args.output.exists())

    def test_input_edits_cannot_reuse_old_pin(self):
        self.register()
        self.source.write_text(self.original.replace(": True", ": False"))
        with self.assertRaisesRegex(ValueError, "SHA256"):
            TaskSpec.load(self.args.output)

    def test_audit_target_cannot_be_a_different_imported_theorem(self):
        self.args.target = "OtherNamespace.t"
        with self.assertRaisesRegex(ValueError, "target does not match"):
            self.register()
        self.assertFalse(self.args.output.exists())

    def test_registered_statement_changes_are_fatal_but_body_drift_is_environment_error(self):
        task = self.register()
        self.source.write_text(self.original.replace(": True", ": False"))
        with self.assertRaises(StatementMismatch):
            TaskSpec.load(self.args.output)
        with self.assertRaises(StatementMismatch):
            task.assert_statement()
        self.source.write_text(self.original.replace("exact True.intro", "trivial"))
        with self.assertRaises(EnvironmentMismatch):
            TaskSpec.load(self.args.output)
        # The proposition/context is still fixed even though the immutable input changed.
        task.assert_statement()

    def test_scope_preservation_checks_candidate_and_mutated_target(self):
        task = self.register()
        task.assert_statement(task.assemble("by trivial"))
        with self.assertRaises(StatementMismatch):
            task.assert_statement(task.assemble("by trivial").replace(": True", ": False"))
        task.config["target"] = "Other.t"
        with self.assertRaises(StatementMismatch):
            task.assert_statement()

    def test_nonfinite_or_fractional_budgets_are_rejected(self):
        self.register()
        original = json.loads(self.args.output.read_text())
        for field, value in (("task_seconds", float("inf")), ("lean_seconds", float("nan")),
                             ("repair_calls", 1.5), ("max_heartbeats", 2.5), ("model_tokens", -1)):
            with self.subTest(field=field):
                config = original | {"limits": original["limits"] | {field: value}}
                write_json(self.args.output, config)
                with self.assertRaises(ValueError):
                    TaskSpec.load(self.args.output)

    def test_axiom_policy_has_an_explicit_list_contract(self):
        self.register()
        original = json.loads(self.args.output.read_text())
        for policy in (None, "Classical.choice", [[]], [""], [123]):
            with self.subTest(policy=policy):
                write_json(self.args.output, original | {"allowed_axioms": policy})
                with self.assertRaisesRegex(ValueError, "allowed_axioms"):
                    TaskSpec.load(self.args.output)
        write_json(self.args.output, original | {"allowed_axioms": []})
        self.assertEqual(TaskSpec.load(self.args.output).config["allowed_axioms"], [])
