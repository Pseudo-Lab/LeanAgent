"""Real Lean/Lake integration; no network inference or paid model calls.

Artifacts stay in a printed temporary directory for inspection. Tests skip only
when the explicitly tested toolchain is unavailable; no toolchain is downloaded.
"""
from pathlib import Path
import json
import shutil
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock

from week4.lean_repair.contracts import TaskSpec, digest, write_json
from week4.lean_repair.lean import LeanVerifier
from week4.lean_repair.runtime import ProcessRunner, Trace


class EnvironmentShapeTests(unittest.TestCase):
    def test_malformed_manifest_returns_environment_error_before_lean(self):
        malformed = [[], None, {"packages": None}, {"packages": {}},
                     {"packages": [None]}, {"packages": ["git"]},
                     {"packagesDir": None}, {"packagesDir": 42},
                     {"packages": [{"type": "git"}]},
                     {"packages": [{"type": "git", "name": 42, "rev": "pinned"}]}]
        with tempfile.TemporaryDirectory(prefix="lean_repair_manifest_") as directory:
            project = Path(directory)
            source = project / "source.lean"
            source.write_text("theorem test : True := by trivial\n")
            (project / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
            manifest = project / "lake-manifest.json"
            for data in malformed:
                with self.subTest(manifest=data):
                    manifest.write_text(json.dumps(data))
                    task = SimpleNamespace(task_id="invalid_manifest", text=source.read_text(), source=source,
                                           project=project, assert_statement=lambda: None,
                                           config={"pins": {"source_sha256": digest(source.read_bytes()),
                                                            "toolchain": "leanprover/lean4:v4.31.0",
                                                            "manifest_sha256": digest(manifest.read_bytes())}})
                    runner = SimpleNamespace(trace=SimpleNamespace(directory=project / "run"), remaining=120)
                    verifier = LeanVerifier(task, runner)
                    verifier._run = Mock(side_effect=AssertionError("Lean must not run for malformed manifest"))
                    result = verifier.prepare()
                    self.assertEqual(result.status, "environment_error", result.to_dict())
                    self.assertTrue(result.detail)
                    verifier._run.assert_not_called()
                    json.dumps(result.to_dict())  # Controller can persist the stop record.


class LeanIntegrationTests(unittest.TestCase):
    versions = ("4.31.0", "4.33.0-rc2")

    @classmethod
    def setUpClass(cls):
        if not shutil.which("elan"):
            raise unittest.SkipTest("elan is unavailable")
        cls.root = Path(tempfile.mkdtemp(prefix="lean_repair_integration_"))
        print("Lean integration artifacts:", cls.root)
        cls.projects = {}
        installed = subprocess.run(["elan", "toolchain", "list"], capture_output=True,
                                   text=True, check=True).stdout
        for version in cls.versions:
            toolchain = "leanprover/lean4:v" + version
            if toolchain not in installed:
                continue
            project = cls.root / version / "project"
            project.mkdir(parents=True)
            (project / "lean-toolchain").write_text(toolchain + "\n")
            (project / "lakefile.toml").write_text('name = "repairIntegration"\nversion = "0.1.0"\n')
            subprocess.run(["elan", "run", toolchain, "lake", "env", "lean", "--version"],
                           cwd=project, capture_output=True, text=True, check=True, timeout=30)
            cls.projects[version] = project
        if not cls.projects:
            raise unittest.SkipTest("Lean 4.31.0 and 4.33.0-rc2 are unavailable")

    def fixture(self, version, name, declaration, body, prefix="", suffix="", reference=None, limits=None):
        project = self.projects[version]
        base = self.root / version / name
        base.mkdir()
        text = "import Std\n\n" + prefix + "namespace Examples\n" + declaration + " := " + body + "\n\nend Examples\n" + suffix
        source = base / "input.lean"
        source.write_text(text)
        manifest = project / "lake-manifest.json"
        start = text.index(declaration)
        body_start = start + len(declaration) + len(" := ")
        config = {"task_id": name, "source": "input.lean", "project": str(project),
                  "target": "Examples." + declaration.split("theorem ", 1)[1].split()[0],
                  "span": {"declaration_start": start, "body_start": body_start,
                           "body_end": body_start + len(body)},
                  "pins": {"source_sha256": digest(text), "toolchain": "leanprover/lean4:v" + version,
                           "manifest_sha256": digest(manifest.read_bytes()) if manifest.exists() else None},
                  "limits": {"lean_seconds": 20, "setup_seconds": 120, "task_seconds": 120,
                             "heartbeats": None}}
        config["limits"].update(limits or {})
        if reference is not None:
            reference_text = text[:body_start] + reference + text[body_start + len(body):]
            (base / "reference.lean").write_text(reference_text)
            config["reference"] = "reference.lean"
            config["pins"]["reference_sha256"] = digest(reference_text)
        write_json(base / "task.json", config)
        task = TaskSpec.load(base / "task.json")
        trace = Trace(base / "run")
        verifier = LeanVerifier(task, ProcessRunner(trace, 120))
        prepared = verifier.prepare()
        self.assertEqual(prepared.status, "candidate_pass", prepared.to_dict())
        return task, verifier

    def test_two_problems_and_feedback(self):
        for version in self.projects:
            with self.subTest(version=version):
                bad = "by\n  exact And.intro h.1 h.2"
                task, verifier = self.fixture(version, "swap", "theorem and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P", bad)
                broken = verifier.verify(bad, "initial")
                self.assertEqual(broken.status, "proof_error", broken.to_dict())
                self.assertTrue(any(d.get("position") and d.get("end_position") for d in broken.diagnostics))
                self.assertTrue(any(d.get("expected_actual_types") for d in broken.diagnostics))
                self.assertEqual(broken.goals, ["Q ∧ P"])
                self.assertIn("h : P ∧ Q", broken.local_context[0])
                self.assertTrue(any(d.get("failed_tactic") == "exact And.intro h.1 h.2" for d in broken.diagnostics))
                fixed = "by\n  exact And.intro h.2 h.1"
                checked = verifier.verify(fixed, "fixed")
                self.assertEqual(checked.status, "candidate_pass", checked.to_dict())
                self.assertGreater(checked.metrics["proof_tokens"], 0)
                self.assertGreater(checked.metrics["raw_heartbeats"], 0)
                final = verifier.verify(fixed, "final", "final")
                self.assertEqual(final.status, "verified", final.to_dict())
                self.assertEqual(final.statement_check, "fixed_context_preserved")
                self.assertEqual((verifier.out / "successful.lean").read_text(), task.assemble(fixed))
                self.assertEqual(task.source.read_text(), task.text)
                self.assertTrue(Path(final.raw_log_path).exists())
                task2, verifier2 = self.fixture(version, "nat", "private theorem nat_identity (n : Nat) : n + 0 = n", "by\n  exact Nat.zero",
                                               prefix="/- nested /- comment -/\nimport Missing.NotAnImport\n-/\n")
                self.assertEqual(verifier2.verify(task2.initial_body, "initial").status, "proof_error")
                natural = verifier2.verify("by\n  simp", "nat_fixed", "final")
                self.assertEqual(natural.status, "verified", natural.to_dict())
                self.assertNotIn("sorryAx", natural.axioms)
                unknown = verifier2.verify("by\n  exact maxHeartbeats", "unknown")
                self.assertEqual(unknown.status, "proof_error", unknown.to_dict())

    def test_guards_axioms_warnings_and_limits(self):
        for version in self.projects:
            with self.subTest(version=version):
                task, verifier = self.fixture(version, "policy", "theorem policy : True", "by\n  exact True.intro")
                for index, body in enumerate(("by\n  sorry", "by\n  set_option maxHeartbeats 0 in\n    exact True.intro",
                                              "by\n  run_tac pure ()", "by\n  exact True.intro\n\ntheorem injected : True := by trivial")):
                    rejected = verifier.verify(body, "rejected" + str(index))
                    self.assertEqual(rejected.status, "invalid_candidate", rejected.to_dict())
                # Alternative --proof-body uses label initial, but still receives the guard.
                self.assertEqual(verifier.verify("by\n  sorry", "initial").status, "invalid_candidate")
                plain = verifier.verify("by\n  -- sorry run_tac are comments\n  exact True.intro", "comments")
                self.assertEqual(plain.status, "candidate_pass", plain.to_dict())
                self.assertEqual(plain.metrics["proof_tokens"], 3)
                task.limits["proof_tokens"] = 1
                self.assertEqual(verifier.verify(task.initial_body, "token_cap").status, "resource_limit")
                task.limits.pop("proof_tokens")
                task.limits["heartbeats"] = 1
                self.assertEqual(verifier.verify(task.initial_body, "heartbeat_cap").status, "resource_limit")
                task.limits.pop("heartbeats")
                task.limits["max_heartbeats"] = 1
                self.assertEqual(verifier.verify("by\n  simp", "native_cap").status, "resource_limit")
                task.limits["max_heartbeats"] = 200000
                task.source.write_text(task.text + "-- changed\n")
                changed = verifier.verify(task.initial_body, "changed")
                self.assertEqual(changed.status, "statement_mismatch", changed.to_dict())
                self.assertEqual(changed.statement_check, "mismatch")

                _, incomplete = self.fixture(version, "transitive", "theorem depends_on_hidden : True", "by\n  exact hidden",
                                             prefix="theorem hidden : True := by sorry\n")
                checked = incomplete.verify(incomplete.task.initial_body, "transitive")
                self.assertEqual(checked.status, "incomplete", checked.to_dict())
                self.assertIn("sorryAx", checked.axioms)
                _, axiom = self.fixture(version, "axiom", "theorem depends_on_axiom : True", "by\n  exact hidden",
                                       prefix="axiom hidden : True\n")
                self.assertEqual(axiom.verify(axiom.task.initial_body, "axiom").status, "invalid_candidate")
                _, warning = self.fixture(version, "warning", "theorem unused_argument (unused : Nat) : True", "by\n  exact True.intro",
                                         prefix="set_option linter.unusedVariables true\n")
                checked = warning.verify(warning.task.initial_body, "warning", "final")
                self.assertEqual(checked.status, "verified", checked.to_dict())
                self.assertTrue(any(d["severity"] == "warning" for d in checked.diagnostics))
                _, reference = self.fixture(version, "reference", "theorem reference_identity (n : Nat) : n + 0 = n",
                                            "by\n  exact Nat.zero", reference="by\n  simp",
                                            limits={"proof_tokens": 1, "heartbeats": 1, "max_heartbeats": 1})
                self.assertGreater(reference.reference_metrics["proof_tokens"], 1)
                self.assertGreater(reference.reference_metrics["raw_heartbeats"], 1000)
                if getattr(reference.task, "reference_source", None):
                    reference.task.reference_source.write_text("-- changed\n")
                    self.assertEqual(reference.verify(reference.task.initial_body, "changed_reference").status,
                                     "environment_error")

    def test_native_nested_tactic_feedback_and_incompleteness(self):
        proofs = {
            "bullet": ("by\n  constructor\n  · exact h.1\n  · exact h.1", "Q", "exact h.1"),
            "case": ("by\n  constructor\n  case left =>\n    exact h.1\n  case right =>\n    exact h.1", "Q", "exact h.1"),
            "multiline": ("by\n  exact And.intro\n    h.1\n    h.2", "Q ∧ P", "exact And.intro\n    h.1\n    h.2"),
            "nested": ("by\n  have first : Q := by\n    exact h.1\n  exact ⟨first, h.1⟩", "Q", "exact h.1"),
        }
        for version in self.projects:
            for name, (body, goal, tactic) in proofs.items():
                with self.subTest(version=version, syntax=name):
                    task, verifier = self.fixture(version, name, "theorem feedback (P Q : Prop) (h : P ∧ Q) : Q ∧ P", body)
                    broken = verifier.verify(body, "initial")
                    self.assertEqual(broken.status, "proof_error", broken.to_dict())
                    self.assertEqual(broken.goals, [goal], broken.to_dict())
                    diagnostic = next(d for d in broken.diagnostics if d.get("failed_tactic"))
                    self.assertEqual(diagnostic["failed_tactic"], tactic)
                    self.assertIn("h : P ∧ Q", broken.local_context[0])
                    span = diagnostic["tactic_range"]
                    original = task.assemble(body)
                    self.assertEqual(original[span["start_offset"]:span["end_offset"]], tactic)
                    self.assertEqual(diagnostic["source_text"], original[diagnostic["start_offset"]:diagnostic["end_offset"]])
                    self.assertEqual(diagnostic["proof_state_source"], "lean_infotree_before_tactic")
            with self.subTest(version=version, syntax="unsolved_and_mixed"):
                body = "by\n  constructor\n  · exact h.2"
                _, verifier = self.fixture(version, "unsolved", "theorem partial_proof (P Q : Prop) (h : P ∧ Q) : Q ∧ P", body)
                partial = verifier.verify(body, "initial")
                self.assertEqual(partial.status, "incomplete", partial.to_dict())
                self.assertEqual(partial.failure_kind, "unsolved_goals")
                self.assertEqual(partial.goals, ["P"], partial.to_dict())
                self.assertIn("h : P ∧ Q", partial.local_context[0])
                mixed = verifier.verify("by\n  constructor\n  · exact h.1", "mixed")
                self.assertEqual(mixed.status, "proof_error", mixed.to_dict())
                self.assertTrue(any(d.get("message", "").startswith("unsolved goals") for d in mixed.diagnostics))
                self.assertEqual(mixed.goals, ["Q"])
            with self.subTest(version=version, syntax="sorry_positions"):
                _, verifier = self.fixture(version, "sorry_positions", "theorem unfinished : True", "by\n  sorry")
                incomplete = verifier.verify(verifier.task.initial_body, "initial")
                self.assertEqual(incomplete.status, "incomplete", incomplete.to_dict())
                explicit = [s for s in incomplete.sorries if s["kind"] == "explicit_sorry"]
                self.assertEqual(len(explicit), 1)
                self.assertEqual(explicit[0]["source_text"], "sorry")
                self.assertEqual(explicit[0]["end_offset"] - explicit[0]["start_offset"], 5)
                self.assertTrue(any(s["kind"] == "transitive_dependency" for s in incomplete.sorries))

    def test_native_unicode_ranges(self):
        for version in self.projects:
            with self.subTest(version=version, syntax="unicode_positions"):
                body = "by\n  have α : P := h₁.1\n  exact And.intro α h₁.2"
                task, verifier = self.fixture(version, "unicode_positions",
                                              "theorem unicode_feedback (P Q : Prop) (h₁ : P ∧ Q) : Q ∧ P", body)
                checked = verifier.verify(body, "initial")
                self.assertEqual(checked.status, "proof_error", checked.to_dict())
                diagnostic = next(d for d in checked.diagnostics if d.get("failed_tactic"))
                self.assertEqual(diagnostic["failed_tactic"], "exact And.intro α h₁.2")
                self.assertEqual(checked.goals, ["Q ∧ P"])
                self.assertIn("α : P", checked.local_context[0])
                source = task.assemble(body)
                self.assertEqual(source[diagnostic["start_offset"]:diagnostic["end_offset"]],
                                 diagnostic["source_text"])
                # The actual CLI span points at the failing Unicode argument.
                self.assertEqual(diagnostic["source_text"], "α")
                self.assertEqual(source.encode()[diagnostic["start_byte_offset"]:diagnostic["end_byte_offset"]].decode(), "α")


if __name__ == "__main__":
    unittest.main()
