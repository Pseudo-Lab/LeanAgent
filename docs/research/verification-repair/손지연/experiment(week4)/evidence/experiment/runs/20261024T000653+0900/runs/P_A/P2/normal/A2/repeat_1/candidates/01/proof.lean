by
  intro h
  induction h <;>
    simp_all [List.Subset, extractOldExprVars,
      Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] <;>
    grind