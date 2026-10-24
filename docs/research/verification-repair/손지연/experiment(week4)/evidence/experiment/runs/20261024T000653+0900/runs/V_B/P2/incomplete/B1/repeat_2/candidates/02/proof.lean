by
  intro Hnorm
  induction post <;>
    cases Hnorm <;>
    simp_all [extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars,
      List.Subset] <;>
    grind