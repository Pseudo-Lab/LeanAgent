by
  intro _
  induction post <;>
    simp_all [extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars,
      List.Subset] <;>
    grind