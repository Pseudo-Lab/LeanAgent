"""Guard tests with synthetic proofs and mocked Lean execution; no downloads."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / 'run_search.py'
spec = importlib.util.spec_from_file_location('search_tests_runner', SCRIPT)
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)


class SearchTests(unittest.TestCase):
    def setUp(self):
        scratch = Path(os.environ['CLAUDE_JOB_DIR']) / 'tmp' if os.environ.get('CLAUDE_JOB_DIR') else None
        self.temp = tempfile.TemporaryDirectory(dir=scratch)
        self.root = Path(self.temp.name)
        self.repo = self.root / 'repo'
        self.repo.mkdir()
        self.row = {'statement': 'theorem demo : True', 'src': 'theorem demo : True := by\n  trivial', 'file_path': 'Proof.lean'}
        (self.repo / 'Proof.lean').write_text(self.row['src'])
        self.start = self.root / 'start.lean'
        self.start.write_text('theorem demo : True := by\n  exact True.intro\n')
        self.patches = [patch.object(s, 'OUTPUT', self.root / 'metrics'),
                        patch.object(s.base, 'problem', return_value=self.row),
                        patch.object(s, 'fingerprint', return_value={'version': 'mock', 'files': {}})]
        for p in self.patches:
            p.start()
        with s.lock():
            s.initialize(8, self.repo, self.start)
        self.target = s.folder(8)

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.temp.cleanup()

    def proposal(self, number=1):
        candidate = self.root / f'candidate{number}.lean'
        candidate.write_text(f'theorem demo : True := by\n  -- variant {number}\n  exact True.intro\n')
        hypothesis = self.root / f'hypothesis{number}.json'
        s.write(hypothesis, {'problem': 'P8', 'strategy': 'mock', 'rationale': 'guard testing',
                            'parent': {'path': str(self.start), 'sha256': s.sha(self.start)}})
        return candidate, hypothesis

    def fake_evaluate(self, args, output_dir):
        output_dir.mkdir()
        result = {'status': 'passed', 'valid': True, 'heartbeat': 100, 'proof_tokens': 12,
                  'axioms': ['propext']}
        s.write(output_dir / 'result.json', result)
        (output_dir / 'check.log').write_text('')
        return result

    def controls(self):
        with patch.object(s.base, 'evaluate', side_effect=self.fake_evaluate):
            self.assertEqual(s.run(8, 'reference', 1)['status'], 'passed')
            self.assertEqual(s.run(8, 'start', 1)['status'], 'passed')

    def test_lock_exclusion(self):
        with s.lock():
            with self.assertRaises(FileExistsError):
                with s.lock():
                    self.fail('second lock acquired')
        self.assertFalse((s.OUTPUT / '.lock').exists())

    def test_no_overwrite(self):
        with self.assertRaises(ValueError):
            s.initialize(8, self.repo, self.start)
        with self.assertRaises(FileExistsError):
            s.write(self.target / 'session.json', {})

    def test_baseline_and_start_gates(self):
        name = s.register(8, *self.proposal())
        with patch.object(s.base, 'evaluate') as evaluate:
            for target in ('start', name):
                with self.assertRaises(ValueError):
                    s.run(8, target, 1)
            evaluate.assert_not_called()
        with patch.object(s.base, 'evaluate', side_effect=self.fake_evaluate):
            s.run(8, 'reference', 1)
            with self.assertRaises(ValueError):
                s.run(8, name, 1)

    def test_budget_including_failed_or_reserved(self):
        for i in range(1, 7):
            self.assertEqual(s.register(8, *self.proposal(i)), f'c{i:03d}')
        with self.assertRaisesRegex(ValueError, 'budget'):
            s.register(8, *self.proposal(7))

    def test_duplicate_normalized_body(self):
        candidate, hypothesis = self.proposal()
        s.register(8, candidate, hypothesis)
        candidate.write_text(candidate.read_text() + '\n')
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            s.register(8, candidate, hypothesis)

    def test_wrong_parent(self):
        candidate, hypothesis = self.proposal()
        data = s.read(hypothesis)
        data['parent']['sha256'] = 'wrong'
        hypothesis.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'Parent hash'):
            s.register(8, candidate, hypothesis)

    def test_changed_candidate_blocks_execution(self):
        name = s.register(8, *self.proposal())
        self.controls()
        (self.target / 'candidates' / name / 'candidate.lean').write_text('changed')
        with patch.object(s.base, 'evaluate') as evaluate:
            self.assertEqual(s.run(8, name, 1)['status'], 'preflight_error')
            evaluate.assert_not_called()
        self.assertTrue((self.target / 'STOP.json').exists())

    def test_environment_failure_stops_theorem(self):
        def failure(args, output_dir):
            result = self.fake_evaluate(args, output_dir)
            result.update(status='failed', valid=False, heartbeat=None, axioms=None)
            (output_dir / 'result.json').write_text(json.dumps(result))
            (output_dir / 'check.log').write_text("object file 'Basic.olean' does not exist")
            return result
        with patch.object(s.base, 'evaluate', side_effect=failure) as evaluate:
            self.assertEqual(s.run(8, 'reference', 1)['status'], 'environment_error')
            with self.assertRaises(ValueError):
                s.run(8, 'reference', 2)
            self.assertEqual(evaluate.call_count, 1)

    def test_interrupted_original_blocks(self):
        (self.target / 'runs/reference-1').mkdir(parents=True)
        with self.assertRaisesRegex(ValueError, 'interrupted'):
            s.run(8, 'reference', 2)

    def test_missing_raw_result_is_tool_error(self):
        with patch.object(s.base, 'evaluate', return_value={'status': 'passed'}):
            self.assertEqual(s.run(8, 'reference', 1)['status'], 'tool_error')

    def test_post_run_drift_never_passes(self):
        with patch.object(s.base, 'evaluate', side_effect=self.fake_evaluate), patch.object(s, 'unchanged', side_effect=[None, OSError('removed dependency')]):
            self.assertEqual(s.run(8, 'reference', 1)['status'], 'fingerprint_or_input_drift')
        self.assertEqual(s.read(self.target / 'runs/reference-1/raw/result.json')['status'], 'passed')

    def test_axiom_and_measurement_guards(self):
        result = {'status': 'passed', 'valid': True, 'heartbeat': 10, 'axioms': ['propext', 'Classical.choice']}
        self.assertEqual(s.classify(result, '', ['propext']), 'new_axioms')
        result['axioms'] = ['propext']
        result['heartbeat'] = None
        self.assertEqual(s.classify(result, '', ['propext']), 'measurement_failed')
        result.update(status='timeout', valid=False)
        self.assertEqual(s.classify(result, '', []), 'timeout')

    def test_repetitions_and_three_run_summary(self):
        self.controls()
        with self.assertRaises(FileExistsError):
            s.run(8, 'reference', 1)
        self.assertIsNone(s.summarize(8)['comparisons']['reference']['median_heartbeat'])
        with patch.object(s.base, 'evaluate', side_effect=self.fake_evaluate):
            with self.assertRaises(ValueError):
                s.run(8, 'start', 3)
            for name in ('reference', 'start'):
                for repetition in (2, 3):
                    s.run(8, name, repetition)
        result = s.summarize(8)['comparisons']['start']
        self.assertEqual(result['median_heartbeat'], 100)
        self.assertEqual(result['range_heartbeat'], [100, 100])
        self.assertEqual(result['heartbeat_reduction_vs_reference_pct'], 0)


if __name__ == '__main__':
    unittest.main()
