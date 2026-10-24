by
  induction post <;>
    simp [substOld, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] at *
  all_goals
    try split <;> try split <;> simp_all <;> grind