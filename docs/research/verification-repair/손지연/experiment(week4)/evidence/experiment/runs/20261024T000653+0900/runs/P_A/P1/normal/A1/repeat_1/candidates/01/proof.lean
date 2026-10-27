by
  induction post <;>
    simp [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] at * <;>
    grind