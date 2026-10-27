"""Run the unchanged archived package from its shared location."""
from pathlib import Path
import runpy
import sys
import types
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent/'verification-repair'
# Original tests use week4.lean_repair. Supply that namespace without editing them.
week4 = types.ModuleType('week4'); week4.__path__=[str(ROOT)]
sys.modules['week4']=week4

def main():
    if len(sys.argv)<2 or sys.argv[1] not in ('cli','unit'):
        print('Usage: python3.12 evidence/reproduce.py cli --help | unit')
        return
    if sys.argv[1]=='cli':
        sys.argv=sys.argv[:1]+sys.argv[2:]
        runpy.run_module('week4.lean_repair',run_name='__main__')
    else:
        sys.path.insert(0,str(ROOT/'tests'))
        names=['test_controller','test_diagnostics','test_model','test_task','test_runtime']
        result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromNames(names))
        raise SystemExit(0 if result.wasSuccessful() else 1)

if __name__=='__main__':main()
