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
  have combine {a b c d : List CoreIdent}
      (ha : a.Subset (c ++ [h1])) (hb : b.Subset (d ++ [h1])) :
      (a ++ b).Subset ((c ++ d) ++ [h1]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp (ha hx) with hx | hx
      · exact List.mem_append_left _ (List.mem_append_left _ hx)
      · exact List.mem_append_right _ hx
    · rcases List.mem_append.mp (hb hx) with hx | hx
      · exact List.mem_append_left _ (List.mem_append_right _ hx)
      · exact List.mem_append_right _ hx
  induction post with
  | const | bvar | op => exact List.Subset.empty
  | fvar => exact List.subset_append_left _ _
  | abs _ _ _ ih => exact ih
  | quant _ _ _ _ _ ih1 ih2 => exact combine ih1 ih2
  | ite _ _ _ _ ih1 ih2 ih3 => exact combine (combine ih1 ih2) ih3
  | eq _ _ _ ih1 ih2 => exact combine ih1 ih2
  | app _ fn arg ihfn iharg =>
    unfold substOld
    split
    · split <;> simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars, List.Subset]
    · exact combine ihfn iharg
#print axioms target
end WarmupMeasure
