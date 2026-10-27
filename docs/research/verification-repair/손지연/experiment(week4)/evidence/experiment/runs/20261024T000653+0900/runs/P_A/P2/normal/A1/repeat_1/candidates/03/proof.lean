by
  intro Hnorm
  induction post <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
      Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
  case app fn e fn_ih e_ih =>
    unfold extractOldExprVars
    split
    · simp [Lambda.LExpr.LExpr.getVars]
      intro x Hin
      exact Hin
    · next Hfalse =>
      cases Hnorm with
      | app Hfn He Hnold =>
        exfalso
        specialize Hnold (by constructor)
        cases Hnold
        exact Hfalse rfl
    · cases Hnorm with
      | app Hfn He _ =>
        apply List.append_subset.mpr
        exact ⟨fn_ih Hfn, e_ih He⟩
  case abs ih =>
    cases Hnorm
    apply ih <;> assumption
  case quant trih eih =>
    cases Hnorm
    apply List.append_subset.mpr
    constructor
    · apply trih <;> assumption
    · apply eih <;> assumption
  case ite cih tih eih =>
    cases Hnorm
    apply List.append_subset.mpr
    constructor
    · apply cih <;> assumption
    · apply List.append_subset.mpr
      constructor
      · apply tih <;> assumption
      · apply eih <;> assumption
  case eq ih1 ih2 =>
    cases Hnorm
    apply List.append_subset.mpr
    constructor
    · apply ih1 <;> assumption
    · apply ih2 <;> assumption