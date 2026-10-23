import unittest
from minimize import patch, sites, suggestion, score, eligible

class SafetyTests(unittest.TestCase):
    def test_utf8_offsets(self):
        body='by\n  have hα : α = α := rfl\n  exact hα'
        a=body.encode().index(b'have');b=body.encode().index(b'\n',a)
        self.assertEqual(patch(body,a,b,'rfl'),'by\n  rfl\n  exact hα')

    def test_non_tactic_nodes_and_inline_branches_excluded(self):
        body='by\n  exact hh\n  case x => exact hh'
        raw=body.encode();a=raw.index(b'exact');b=a+8;c=raw.rindex(b'exact')
        nodes=[{'kind':'Lean.Parser.Tactic.exact','start':a,'end':b,'depth':1},
               {'kind':'Lean.Parser.Tactic.simpLemma','start':a,'end':b,'depth':1},
               {'kind':'Lean.Parser.Tactic.exact','start':c,'end':c+8,'depth':1}]
        out=sites(body,nodes)
        self.assertEqual(len(out),1);self.assertEqual(out[0]['kind'],'Lean.Parser.Tactic.exact')

    def test_suggestion_location_and_sorry(self):
        out='x.lean:4:2: information: Try this:\n  [apply] exact h\nx.lean:8:2: information: Try this: sorry'
        self.assertEqual(suggestion(out,4),'exact h')
        self.assertIsNone(suggestion(out,5));self.assertIsNone(suggestion(out,8))

    def test_shorter_can_be_worse(self):
        self.assertLess(score(50,200,100,100),score(100,100,100,100))

    def test_robustness_cost(self):
        self.assertAlmostEqual(score(50,50,100,100,1,2),50)

    def test_new_axioms_and_missing_measurements(self):
        base={'axioms':['propext']}
        self.assertFalse(eligible({'kind':'valid','heartbeats':1,'axioms':['Classical.choice']},base))
        self.assertFalse(eligible({'kind':'valid','heartbeats':None,'axioms':[]},base))
        self.assertTrue(eligible({'kind':'valid','heartbeats':1,'axioms':[]},base))

if __name__=='__main__':unittest.main()
