by
  induction post <;>
    simp_all [List.Subset, substOld, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] <;>
    grind