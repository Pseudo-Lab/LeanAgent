by
  intro v Hin
  induction post <;>
    simp [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] at * <;>
    grind