by
  intro Hnorm
  induction Hnorm <;>
    simp_all [extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars,
      List.Subset] <;>
    grind