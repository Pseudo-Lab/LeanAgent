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
theorem target:
  (Imperative.HasVarsPure.getVars (P:=Expression)
    (substOld h2 (Lambda.LExpr.fvar m h1 ty) post)).Subset
    (Imperative.HasVarsPure.getVars (P:=Expression) post ++ [h1]) := by
  induction post <;> unfold substOld <;> (try split <;> try split) <;>
    simp_all [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] <;>
    (repeat' apply List.Subset.app) <;> (try (apply List.Subset.trans; assumption)) <;>
    simp +contextual [List.Subset, or_imp]
#print axioms target
end WarmupMeasure
