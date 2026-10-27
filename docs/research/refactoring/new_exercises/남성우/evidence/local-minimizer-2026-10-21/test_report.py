import unittest
from report import assessed

class ScoreCoverageTests(unittest.TestCase):
    def setUp(self):
        self.versions=['v1','v2']
        self.base={v:{'kind':'valid','tokens':100,'heartbeats':100,'axioms':['propext']} for v in self.versions}
        self.obs={v:{'kind':'valid','tokens':50,'heartbeats':50,'axioms':[]} for v in self.versions}

    def test_unchecked_and_timeout_are_not_failure(self):
        self.assertIsNone(assessed('by rfl',{'v1':self.obs['v1']},self.base,self.versions))
        self.obs['v2']={'kind':'timeout'}
        self.assertIsNone(assessed('by rfl',self.obs,self.base,self.versions))

    def test_observed_version_failure_reduces_score(self):
        self.obs['v2']={'kind':'invalid'}
        self.assertAlmostEqual(assessed('by rfl',self.obs,self.base,self.versions),50)

    def test_axiom_increase_on_secondary_rejected(self):
        self.obs['v2']['axioms']=['Classical.choice']
        self.assertIsNone(assessed('by rfl',self.obs,self.base,self.versions))

if __name__=='__main__':unittest.main()
