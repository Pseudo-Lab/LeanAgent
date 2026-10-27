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
    · next hfalse =>
      cases Hnorm with
      | app hfn he hn =>
        exfalso
        apply hn
        constructor
        cases hn
        exact hfalse rfl
    · cases Hnorm
      grind
  all_goals cases Hnorm <;> grind