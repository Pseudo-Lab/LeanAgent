by
  induction post <;>
    simp_all [OldExpressions.substOld, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] <;>
    grind