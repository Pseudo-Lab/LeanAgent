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
  have combine {a b c d : List CoreIdent}
      (ha : a.Subset c) (hb : b.Subset d) : (a ++ b).Subset (c ++ d) :=
    fun _ hx => (List.mem_append.mp hx).elim
      (fun hx => List.mem_append_left _ (ha hx))
      (fun hx => List.mem_append_right _ (hb hx))
  intro h
  induction h with
  | const | op | bvar | fvar => exact List.Subset.empty
  | abs _ ih => exact ih
  | quant _ _ ih1 ih2 => exact combine ih1 ih2
  | ite _ _ _ ih1 ih2 ih3 => exact combine (combine ih1 ih2) ih3
  | eq _ _ ih1 ih2 => exact combine ih1 ih2
  | app hfn harg hold ihfn iharg =>
    unfold extractOldExprVars
    split
    · exact fun _ hx => hx
    · next hfalse =>
      cases hold .oldPred
      exact False.elim (hfalse _ _ _ rfl)
    · exact combine ihfn iharg
#print axioms target
end WarmupMeasure
