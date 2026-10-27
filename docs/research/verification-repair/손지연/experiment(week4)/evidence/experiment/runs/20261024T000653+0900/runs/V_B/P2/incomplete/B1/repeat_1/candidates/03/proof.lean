by
  intro Hnorm
  induction Hnorm <;>
    simp_all [extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars,
      List.Subset]
  case app =>
    try unfold extractOldExprVars
    repeat
      split <;>
        simp_all [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars,
          List.Subset]
  all_goals grind