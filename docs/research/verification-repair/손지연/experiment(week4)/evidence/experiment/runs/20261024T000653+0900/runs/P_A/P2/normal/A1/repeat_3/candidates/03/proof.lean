by
  intro h
  induction h <;>
    simp_all [OldExpressions.extractOldExprVars,
      Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars,
      List.Subset] <;>
    grind