by
  intro Hnorm
  induction Hnorm
  case app =>
    unfold extractOldExprVars
    split <;>
      simp_all [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars, List.Subset]
  all_goals
    simp_all [extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset]