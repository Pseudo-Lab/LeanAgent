by
  induction post <;>
    simp_all [substOld, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset]
  case app =>
    split
    · split <;>
        simp_all [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars, List.Subset]
    · grind
  all_goals grind