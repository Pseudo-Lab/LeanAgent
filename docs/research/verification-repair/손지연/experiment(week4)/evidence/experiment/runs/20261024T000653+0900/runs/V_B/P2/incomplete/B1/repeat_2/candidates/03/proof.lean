by
  intro Hnorm
  induction Hnorm
  case app fn e m Hnfn Hne Hwf ih1 ih2 =>
    cases fn <;> cases e <;>
      simp_all [extractOldExprVars,
        Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars,
        List.Subset]
  all_goals
    simp_all [extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars,
      List.Subset]