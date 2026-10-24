by
  induction post <;>
    simp only [OldExpressions.substOld, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset, List.mem_append,
      List.mem_singleton] at *
  case app m fn e fnih eih =>
    split
    · split <;>
        simp [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars, List.Subset]
    · simp only [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars, List.Subset, List.mem_append,
          List.mem_singleton] at fnih eih ⊢
      grind
  all_goals grind