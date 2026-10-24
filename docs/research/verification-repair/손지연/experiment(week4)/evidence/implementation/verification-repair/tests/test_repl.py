"""Community protocol checks; optional integration uses a real local REPL.

Set LEAN_REPAIR_REPL_COMMAND to a JSON argv list and LEAN_REPAIR_REPL_TOOLCHAIN
to the matching installed toolchain. These tests never install tools or call APIs.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from week4.lean_repair.contracts import TaskSpec, digest, write_json
from week4.lean_repair.repl import ReplClient, ReplVerifier, normalize_response
from week4.lean_repair.runtime import ProcessRunner, Trace


class ReplNormalizationTests(unittest.TestCase):
    def test_command_pass_does_not_invent_empty_goals(self):
        result = normalize_response({"env": 0})
        self.assertEqual(result.status, "candidate_pass")
        self.assertIsNone(result.goals)
        self.assertIsNone(result.local_context)
        self.assertIsNone(result.backend_proof_status)

    def test_tactic_completed_is_only_preliminary(self):
        result = normalize_response({"proofState": 1, "goals": [], "proofStatus": "Completed"})
        self.assertEqual(result.status, "candidate_pass")
        self.assertEqual(result.goals, [])
        self.assertEqual(result.local_context, [])
        self.assertEqual(result.backend_proof_status, "Completed")
        self.assertNotEqual(result.status, "verified")

    def test_error_message_wins_over_exit_zero_and_empty_goals(self):
        response = {"env": 0, "goals": [], "messages": [
            {"severity": "error", "data": "Unknown identifier `missing`", "pos": {"line": 1, "column": 20}}]}
        process = {"returncode": 0, "timeout": False, "wall_time_limit": False,
                   "process_error": None}
        checked = normalize_response(response, process=process)
        self.assertEqual(checked.status, "proof_error")
        self.assertEqual(checked.process_exit_code, 0)

    def test_tactic_failure_does_not_invent_goals(self):
        result = normalize_response({"message": "Lean error:\nunknown identifier 'missing'"})
        self.assertEqual(result.status, "proof_error")
        self.assertIsNone(result.goals)
        self.assertEqual(normalize_response({"message": "Unknown proof state."}).status, "process_error")
        unfinished = normalize_response({"message": "Lean error:\nunsolved goals\n⊢ True"})
        self.assertEqual(unfinished.status, "incomplete")
        self.assertIsNone(unfinished.goals)

    def test_sorry_and_incomplete_status_win_over_empty_goals(self):
        result = normalize_response({"proofState": 1, "goals": [], "proofStatus": "Completed",
                                     "sorries": [{"goal": "⊢ True", "proofState": 2}]})
        self.assertEqual(result.status, "incomplete")
        missing = normalize_response({"env": 0, "sorries": [{"proofState": 0}]})
        self.assertEqual(missing.status, "incomplete")
        self.assertIsNone(missing.goals)
        self.assertIsNone(missing.local_context)
        self.assertEqual(result.goals, [])
        self.assertTrue(result.sorries)
        result = normalize_response({"proofState": 1, "goals": [], "proofStatus": "Incomplete: contains sorry"})
        self.assertEqual(result.status, "incomplete")

    def test_nonempty_and_unknown_formatted_goals_are_incomplete(self):
        result = normalize_response({"proofState": 1, "goals": ["h : P\n⊢ Q"], "proofStatus": "Incomplete: open goals remain"})
        self.assertEqual(result.status, "incomplete")
        self.assertEqual(result.goals, ["Q"])
        self.assertEqual(result.local_context, ["h : P"])
        result = normalize_response({"proofState": 1, "goals": ["unfamiliar goal format"]})
        self.assertEqual(result.status, "incomplete")

    def test_unsolved_goals_and_exact_tactic_range(self):
        result = normalize_response({"env": 0, "messages": [{"severity": "error", "data": "unsolved goals\n⊢ True",
                                     "pos": {"line": 3, "column": 5}}], "tactics": [
            {"pos": {"line": 2, "column": 2}, "endPos": {"line": 5, "column": 4},
             "tactic": "constructor\n  · skip", "goals": "h : P\n⊢ True ∧ True"},
            {"pos": {"line": 3, "column": 4}, "endPos": {"line": 3, "column": 8},
             "tactic": "skip", "goals": "h : P\n⊢ True"}]})
        self.assertEqual(result.status, "incomplete")
        self.assertEqual(result.diagnostics[0]["failed_tactic"], "skip")
        self.assertEqual(result.goals, ["True"])
        self.assertEqual(result.local_context, ["h : P"])

    def test_malformed_response_is_not_success(self):
        for response in (None, {}, {"proofState": 1, "goals": "[]"}, {"env": 1, "sorries": None},
                         {"env": -1}, {"env": 0, "proofState": -1}, {"env": 0, "messages": [None]},
                         {"env": 0, "messages": [{"data": "missing severity"}]},
                         {"env": 0, "messages": [{"severity": [], "data": "bad"}]},
                         {"env": 0, "messages": [{"severity": "error", "data": {}}]},
                         {"env": 0, "messages": [{"severity": "error", "data": "bad", "pos": "line 1"}]},
                         {"env": 0, "tactics": [None]},
                         {"env": 0, "tactics": [{"tactic": "skip", "goals": "⊢ True", "pos": {"line": "1", "column": 0}}]},
                         {"env": 0, "sorries": [None]}, {"proofState": 1, "goals": [""]}):
            with self.subTest(response=response):
                self.assertEqual(normalize_response(response).status, "process_error")


class RealReplIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        configured = os.environ.get("LEAN_REPAIR_REPL_COMMAND")
        local = Path("/private/tmp/week4-community-repl-v4.31/.lake/build/bin/repl")
        cls.command = json.loads(configured) if configured else ([str(local)] if local.is_file() else None)
        cls.toolchain = os.environ.get("LEAN_REPAIR_REPL_TOOLCHAIN", "leanprover/lean4:v4.31.0")
        if not cls.command or not shutil.which("elan"):
            raise unittest.SkipTest("set LEAN_REPAIR_REPL_COMMAND to an installed community REPL argv list")
        installed = subprocess.run(["elan", "toolchain", "list"], capture_output=True, text=True, check=True).stdout
        if cls.toolchain not in installed:
            raise unittest.SkipTest("matching REPL toolchain is not installed")
        cls.root = Path(tempfile.mkdtemp(prefix="lean_repair_repl_"))
        cls.project = cls.root / "project"
        cls.project.mkdir()
        (cls.project / "lean-toolchain").write_text(cls.toolchain + "\n")
        (cls.project / "lakefile.toml").write_text('name = "replIntegration"\nversion = "0.1.0"\n')
        subprocess.run(["elan", "run", cls.toolchain, "lake", "env", "lean", "--version"],
                       cwd=cls.project, capture_output=True, check=True, timeout=30)
        print("Community REPL integration artifacts:", cls.root)

    def client(self, label):
        trace = Trace(self.root / label)
        runner = ProcessRunner(trace, 120)
        command = ["elan", "run", self.toolchain, "lake", "env", *self.command]
        return ReplClient(command, runner, self.project, trace.directory / "protocol", 20)

    def test_real_command_file_and_tactic_protocol(self):
        client = self.client("protocol")
        header = "theorem and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by\n"
        good = header + "  exact And.intro h.2 h.1\n"
        bad = header + "  exact And.intro h.1 h.2\n"
        fixed, proc = client.query({"cmd": good, "allTactics": True})
        self.assertEqual(normalize_response(fixed, process=proc).status, "candidate_pass")
        source = self.root / "broken.lean"
        source.write_text(bad)
        broken, proc = client.query({"path": str(source), "allTactics": True})
        normalized = normalize_response(broken, process=proc, source_text=bad)
        self.assertEqual(proc["returncode"], 0)
        self.assertEqual(normalized.status, "proof_error", normalized.to_dict())
        self.assertTrue(any(d.get("expected_actual_types") for d in normalized.diagnostics))
        self.assertTrue(normalized.goals)
        sorry, proc = client.query({"cmd": header + "  sorry\n"})
        self.assertEqual(normalize_response(sorry, process=proc).status, "incomplete")
        state = sorry["sorries"][0]["proofState"]
        split, _ = client.query({"tactic": "constructor", "proofState": state})
        wrong, proc = client.query({"tactic": "exact h.1", "proofState": split["proofState"]})
        error = normalize_response(wrong, process=proc)
        self.assertEqual(error.status, "proof_error")
        self.assertIsNone(error.goals)
        right, _ = client.query({"tactic": "exact h.2", "proofState": split["proofState"]})
        completed, proc = client.query({"tactic": "exact h.1", "proofState": right["proofState"]})
        done = normalize_response(completed, process=proc)
        self.assertEqual(done.backend_proof_status, "Completed")
        self.assertEqual(done.goals, [])
        self.assertEqual(done.status, "candidate_pass")
        admitted, proc = client.query({"tactic": "sorry", "proofState": state})
        self.assertEqual(normalize_response(admitted, process=proc).status, "incomplete")
        original, _ = client.query({"cmd": "#print axioms and_swap", "env": sorry["env"]})
        self.assertIn("sorryAx", json.dumps(original))

    def test_hybrid_backend_and_fresh_cli_final(self):
        base = self.root / "hybrid"
        base.mkdir()
        body = "by\n  exact And.intro h.1 h.2"
        declaration = "theorem swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P := "
        text = declaration + body + "\n"
        source = base / "source.lean"
        source.write_text(text)
        manifest = self.project / "lake-manifest.json"
        config = {"task_id": "repl-swap", "source": "source.lean", "project": str(self.project), "target": "swap",
                  "span": {"declaration_start": 0, "body_start": len(declaration), "body_end": len(text) - 1},
                  "pins": {"source_sha256": digest(text), "toolchain": self.toolchain,
                           "manifest_sha256": digest(manifest.read_bytes()) if manifest.exists() else None},
                  "backend": {"kind": "repl", "command": self.command},
                  "limits": {"lean_seconds": 20, "task_seconds": 120, "setup_seconds": 120}}
        write_json(base / "task.json", config)
        task = TaskSpec.load(base / "task.json")
        trace = Trace(base / "run")
        verifier = ReplVerifier(task, ProcessRunner(trace, 120))
        self.assertEqual(verifier.prepare().status, "candidate_pass")
        bad = verifier.verify(body, "initial")
        self.assertEqual(bad.status, "proof_error", bad.to_dict())
        self.assertTrue(any(d["source"] == "lean_repl" for d in bad.diagnostics))
        self.assertTrue(bad.goals)
        self.assertEqual(next(d for d in bad.diagnostics if d["source"] == "lean_repl")["position"]["line"], 2)
        unknown = verifier.verify("by\n  exact missing_name", "unknown")
        self.assertEqual(unknown.status, "proof_error", unknown.to_dict())
        fixed = "by\n  exact And.intro h.2 h.1"
        observed = verifier.verify(fixed, "fixed")
        self.assertEqual(observed.status, "candidate_pass", observed.to_dict())
        self.assertIn("repl_elapsed_ms", observed.metrics)
        self.assertGreater(observed.metrics["proof_tokens"], 0)
        final = verifier.verify(fixed, "final", "final")
        self.assertEqual(final.status, "verified", final.to_dict())
        self.assertNotIn("repl_elapsed_ms", final.metrics)
        self.assertEqual((trace.directory / "successful.lean").read_text(), task.assemble(fixed))
        self.assertNotIn("sorryAx", final.axioms)
        task.config["backend"]["mode"] = "command"
        command_trace = Trace(base / "run_command_mode")
        command_verifier = ReplVerifier(task, ProcessRunner(command_trace, 120))
        self.assertEqual(command_verifier.prepare().status, "candidate_pass")
        command_checked = command_verifier.verify(fixed, "command_mode")
        self.assertEqual(command_checked.status, "candidate_pass", command_checked.to_dict())
        self.assertIn("repl_elapsed_ms", command_checked.metrics)
        original = ReplClient.verify_request

        def mutate_after_repl(client, request, **identity):
            response = original(client, request, **identity)
            task.source.write_text(task.text.replace(": Q ∧ P :=", ": P ∧ Q :=", 1))
            return response

        with patch.object(ReplClient, "verify_request", mutate_after_repl):
            changed = verifier.verify(fixed, "statement_changed_during_repl")
        self.assertEqual(changed.status, "statement_mismatch", changed.to_dict())
        self.assertEqual(changed.statement_check, "mismatch")
        self.assertEqual(changed.failure_kind, "statement_mismatch")

    def test_mismatched_binary_is_environment_failure_before_model(self):
        other = "leanprover/lean4:v4.33.0-rc2"
        if other == self.toolchain:
            self.skipTest("fixture requires a different toolchain")
        installed = subprocess.run(["elan", "toolchain", "list"], capture_output=True, text=True, check=True).stdout
        if other not in installed:
            self.skipTest("second toolchain is unavailable")
        base = self.root / "mismatch"
        project = base / "project"
        project.mkdir(parents=True)
        (project / "lean-toolchain").write_text(other + "\n")
        (project / "lakefile.toml").write_text('name = "mismatchedRepl"\n')
        text = "theorem t : True := by\n  trivial\n"
        (base / "source.lean").write_text(text)
        config = {"task_id": "repl-version-mismatch", "source": "source.lean", "project": str(project), "target": "t",
                  "span": {"declaration_start": 0, "body_start": text.index("by"), "body_end": len(text) - 1},
                  "pins": {"source_sha256": digest(text), "toolchain": other, "manifest_sha256": None},
                  "backend": {"kind": "repl", "command": self.command}, "limits": {"lean_seconds": 20}}
        write_json(base / "task.json", config)
        task = TaskSpec.load(base / "task.json")
        trace = Trace(base / "run")
        prepared = ReplVerifier(task, ProcessRunner(trace, 120)).prepare()
        self.assertEqual(prepared.status, "environment_error", prepared.to_dict())
        self.assertIn("toolchain probe failed", prepared.detail)


if __name__ == "__main__":
    unittest.main()
