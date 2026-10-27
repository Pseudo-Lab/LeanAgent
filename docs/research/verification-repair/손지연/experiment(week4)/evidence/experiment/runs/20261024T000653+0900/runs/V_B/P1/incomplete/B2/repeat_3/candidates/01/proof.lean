by
  intro x Hin
  induction post <;>
    simp_all [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] <;>
    grind