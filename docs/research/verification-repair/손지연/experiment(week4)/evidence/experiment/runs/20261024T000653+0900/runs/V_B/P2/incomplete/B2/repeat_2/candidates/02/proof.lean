by
  intro Hnorm
  induction Hnorm
  case app fn e m Hnfn Hne Hwf ihfn ihe =>
    by_cases Hold : IsOldPred fn
    · have Hfv := Hwf Hold
      cases Hold
      cases Hfv
      simp_all [extractOldExprVars,
        Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars,
        List.Subset]
    · simp_all [extractOldExprVars,
        Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars,
        List.Subset, Hold]
      grind
  all_goals
    simp_all [extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars,
      List.Subset] <;>
    grind