by
  intros Hnorm
  have appendSubset {a b c d : List Expression.Ident}
      (hac : a.Subset c) (hbd : b.Subset d) :
      (a ++ b).Subset (c ++ d) := by
    intros x hx
    simp only [List.mem_append] at hx ⊢
    exact hx.elim (fun h => Or.inl (hac h)) (fun h => Or.inr (hbd h))
  induction post <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
      Lambda.LExpr.LExpr.getVars] at Hnorm ⊢ <;>
    try simp_all
  case app fn e fn_ih e_ih =>
    unfold extractOldExprVars
    split
    · simp [Lambda.LExpr.LExpr.getVars]
      intros x hx
      exact hx
    · next Hfalse =>
      cases Hnorm with
      | app Hfn He Hold =>
        exfalso
        specialize Hold (by constructor)
        cases Hold
        exact Hfalse rfl
    · cases Hnorm with
      | app Hfn He Hold =>
        exact appendSubset (fn_ih Hfn) (e_ih He)
  case abs ih =>
    cases Hnorm
    apply ih
    assumption
  case quant trih eih =>
    cases Hnorm
    apply appendSubset
    · apply trih
      assumption
    · apply eih
      assumption
  case ite cih tih eih =>
    cases Hnorm
    apply appendSubset
    · apply cih
      assumption
    · apply appendSubset
      · apply tih
        assumption
      · apply eih
        assumption
  case eq ih1 ih2 =>
    cases Hnorm
    apply appendSubset
    · apply ih1
      assumption
    · apply ih2
      assumption