by
  intro Hnorm x Hin
  induction Hnorm <;>
    simp_all [OldExpressions.extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] <;>
    grind