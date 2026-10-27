by
  intro Hnorm
  induction Hnorm
  case app =>
    unfold extractOldExprVars
    split <;>
      simp_all [default, Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars, List.Subset]
    all_goals grind
  all_goals
    simp_all [default, extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset]
    grind