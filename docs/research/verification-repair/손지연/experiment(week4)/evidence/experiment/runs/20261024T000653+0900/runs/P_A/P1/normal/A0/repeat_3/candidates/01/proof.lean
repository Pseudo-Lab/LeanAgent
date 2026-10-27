by
  induction post <;>
    simp_all [substOld, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] <;>
    grind