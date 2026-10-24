by
  induction post <;>
    simp [substOld] <;>
    (try split <;> try split) <;>
    simp_all [List.Subset, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] <;>
    grind