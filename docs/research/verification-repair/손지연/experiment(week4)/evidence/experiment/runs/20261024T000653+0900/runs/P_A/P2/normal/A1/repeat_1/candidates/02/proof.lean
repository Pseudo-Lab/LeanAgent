by
  intro Hnorm
  have append_subset {a b c d : List Expression.Ident}
      (ha : a.Subset c) (hb : b.Subset d) :
      (a ++ b).Subset (c ++ d) := by
    intro x hx
    simp only [List.mem_append] at hx ⊢
    cases hx with
    | inl hx => exact Or.inl (ha hx)
    | inr hx => exact Or.inr (hb hx)
  induction post <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
          Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
  case app fn e fn_ih e_ih =>
    unfold extractOldExprVars
    split
    · simp [Lambda.LExpr.LExpr.getVars]
      intro x hx
      exact hx
    · next Hfalse =>
      cases Hnorm with
      | app Hfn He Hshape =>
        exfalso
        specialize Hshape ?_
        constructor
        cases Hshape
        apply Hfalse
        rfl
    · cases Hnorm with
      | app Hfn He Hshape =>
        exact append_subset (fn_ih Hfn) (e_ih He)
  case abs ih =>
    cases Hnorm
    apply ih <;> assumption
  case quant trih eih =>
    cases Hnorm
    apply append_subset
    · apply trih <;> assumption
    · apply eih <;> assumption
  case ite cih tih eih =>
    cases Hnorm
    apply append_subset
    · apply cih <;> assumption
    · apply append_subset
      · apply tih <;> assumption
      · apply eih <;> assumption
  case eq ih1 ih2 =>
    cases Hnorm
    apply append_subset
    · apply ih1 <;> assumption
    · apply ih2 <;> assumption