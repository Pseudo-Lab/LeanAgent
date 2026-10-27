by
  induction post <;>
    simp only [substOld, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars]
  case app ih₁ ih₂ =>
    split
    · split <;> simp_all [List.Subset] <;> grind
    · simp_all [List.Subset] <;> grind
  all_goals simp_all [List.Subset] <;> grind