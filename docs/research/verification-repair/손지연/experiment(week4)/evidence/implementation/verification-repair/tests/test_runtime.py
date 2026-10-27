from pathlib import Path
import sys
import tempfile
import unittest

from week4.lean_repair.runtime import ProcessRunner, Trace


class RuntimeTests(unittest.TestCase):
    def test_timeout_preserves_partial_streams(self):
        with tempfile.TemporaryDirectory() as root:
            trace = Trace(Path(root) / "run")
            runner = ProcessRunner(trace, 2)
            result = runner.run([sys.executable, "-c", "import time; print('partial',flush=True); time.sleep(5)"],
                                root, trace.directory / "process", .15)
            self.assertTrue(result["timeout"])
            self.assertIn("partial", Path(result["stdout"]).read_text())
            self.assertTrue((trace.directory / "trace.jsonl").exists())

    def test_existing_run_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as root:
            Trace(Path(root) / "run")
            with self.assertRaises(FileExistsError):
                Trace(Path(root) / "run")
