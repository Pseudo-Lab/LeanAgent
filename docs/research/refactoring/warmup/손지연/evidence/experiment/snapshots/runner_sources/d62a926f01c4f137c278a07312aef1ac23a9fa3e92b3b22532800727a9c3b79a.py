"""Experiment-local compatibility for legal Finset cardinality notation."""
from lean_repair.lean import LeanVerifier
import re


class ExperimentVerifier(LeanVerifier):
    def _with_support(self, text):
        result = super()._with_support(text)
        before = 'blockedWords.contains value || value.startsWith "#"'
        after = 'blockedWords.contains value || (value.startsWith "#" && value != "#")'
        assert result.count(before) == 1
        result=result.replace(before, after, 1)
        before='(name.splitOn ".").any (fun p => blockedWords.contains p)'
        after='(name.splitOn ".").any (fun p => blockedWords.contains p && p != "eval")'
        assert result.count(before)==1
        # Polynomial.eval / locally opened eval are ordinary mathematical constants.
        # The eval atom, #commands, Command AST, IO/System/Lean restrictions remain.
        return result.replace(before,after,1)

    def _axioms(self, messages):
        # Lean names can contain apostrophes, e.g. variational_calculus'.
        target=self.task.config['target']
        for diagnostic in reversed(messages):
            match=re.search(r"'(.+)' (depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",str(diagnostic['message']))
            if match and (match[1]==target or match[1].startswith('_private.') and match[1].endswith('.'+target)):
                return sorted(x.strip() for x in (match[3] or '').split(',') if x.strip())
        return None
