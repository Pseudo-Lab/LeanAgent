import Strata.Transform.CallElimCorrect

namespace CallElimCorrect
open Core Core.Transform CallElim

open OldExpressions in
theorem improved_substOldPostSubset:
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
    · split
      · exact List.subset_append_right _ _
      · exact List.subset_append_left _ _
    · exact combine ihfn iharg

open OldExpressions in
theorem improved_extractedOldExprInVars :
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

#print axioms improved_substOldPostSubset
#print axioms improved_extractedOldExprInVars

-- The propositions remain identical to the original declarations.
example : @improved_substOldPostSubset = @substOldPostSubset := by rfl
example : @improved_extractedOldExprInVars = @extractedOldExprInVars := by rfl
end CallElimCorrect
