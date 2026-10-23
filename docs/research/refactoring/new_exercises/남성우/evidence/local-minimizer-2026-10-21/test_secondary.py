"""Regression: robustness checks must not require an unused HB measurement."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import minimize

class SecondaryValidationTests(unittest.TestCase):
    def test_secondary_valid_proof_without_heartbeat_completes(self):
        n=10;version='v4.28.0';row=minimize.ROWS[n-1]
        pin=next(x[version] for x in row['version_info'] if version in x)
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);project=root/'project';project.mkdir()
            (project/'lean-toolchain').write_text('leanprover/lean4:'+version)
            (root/'pool').mkdir();(root/'pool/10.json').write_text('[]')
            with patch.object(minimize,'HERE',root), \
                 patch.object(minimize.v,'context',return_value=('source',0,0,0,'by trivial')), \
                 patch.object(minimize.subprocess,'check_output',return_value=pin), \
                 patch.object(minimize.v,'check',return_value={'kind':'valid','axioms':[],'tokens':3}) as check:
                minimize.run_problem(n,project,version)
            result=json.loads((root/'runs/10'/version/'result.json').read_text())
            self.assertEqual(result['baseline']['kind'],'valid')
            self.assertNotIn('heartbeats',result['baseline'])
            self.assertTrue(all(c.kwargs.get('measure') is False for c in check.call_args_list))

if __name__=='__main__':unittest.main()
