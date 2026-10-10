import Lean
import Strata.Transform.CallElimCorrect
set_option Elab.async false
open Lean Elab Command
elab "#measure " c:command : command => do
  let (_, ticks) ← withHeartbeats (elabCommand c)
  logInfo m!"RAW_HEARTBEATS={ticks}"
namespace WarmupMeasure
open Core Core.Transform CallElim OldExpressions CallElimCorrect
#measure
theorem target :
  NormalizedOldExpr post →
  (extractOldExprVars post).Subset
  (Imperative.HasVarsPure.getVars post) := by
  intro h
  induction h <;> unfold extractOldExprVars <;> (try split) <;>
    simp_all [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] <;>
    (repeat' apply List.Subset.app) <;> (try (apply List.Subset.trans; assumption)) <;>
    simp +contextual [List.Subset]
#print axioms target
end WarmupMeasure
