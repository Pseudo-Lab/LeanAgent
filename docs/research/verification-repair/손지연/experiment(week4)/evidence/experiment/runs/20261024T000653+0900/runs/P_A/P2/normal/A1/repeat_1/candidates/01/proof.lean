by
  intro Hnorm
  induction Hnorm <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
      Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
  case app fn e m Hnfn Hne Hwf fn_ih e_ih =>
    unfold extractOldExprVars
    split
    · simp [Lambda.LExpr.LExpr.getVars]
      intro x Hin
      exact Hin
    · next Hfalse =>
      exfalso
      specialize Hwf (by constructor)
      cases Hwf
      apply Hfalse
      rfl
    · apply List.Subset.app
      · apply List.Subset.trans fn_ih
        intro x Hin
        simp_all
      · apply List.Subset.trans e_ih
        intro x Hin
        simp_all