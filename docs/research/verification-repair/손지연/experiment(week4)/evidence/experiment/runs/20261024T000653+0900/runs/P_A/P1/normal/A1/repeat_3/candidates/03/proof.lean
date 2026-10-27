by
  induction post <;>
    simp [substOld] <;>
    simp_all [Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] <;>
    (try split) <;>
    simp_all [Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] <;>
    (try split) <;>
    simp_all [Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] <;>
    grind