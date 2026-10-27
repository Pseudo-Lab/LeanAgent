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
      intro x hx
      exact hx
    · next hfalse =>
      cases Hnorm with
      | app hfn he hn =>
        exfalso
        specialize hn ?_
        constructor
        cases hn
        apply hfalse
        rfl
    · cases Hnorm
      simp_all [List.Subset]
  all_goals cases Hnorm <;> simp_all [List.Subset]