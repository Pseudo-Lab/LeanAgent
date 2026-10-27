by
  induction post <;> simp only [substOld]
  case app ih₁ ih₂ =>
    split <;> try split <;>
      simp_all [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars, List.Subset] <;>
      grind
  all_goals
    simp_all [Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] <;>
    grind