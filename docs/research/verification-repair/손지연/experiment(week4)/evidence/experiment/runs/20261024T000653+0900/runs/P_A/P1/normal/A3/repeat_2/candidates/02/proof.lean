by
  induction post <;>
    simp_all [substOld, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] <;>
    try split <;>
    try split <;>
    simp_all [Lambda.LExpr.LExpr.getVars] <;>
    grind