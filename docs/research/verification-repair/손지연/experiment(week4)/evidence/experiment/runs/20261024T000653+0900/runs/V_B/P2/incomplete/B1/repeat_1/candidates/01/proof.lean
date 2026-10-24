by
  intro Hnorm
  induction Hnorm <;>
    simp [extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] at * <;>
    grind