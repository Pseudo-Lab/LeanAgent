by
  intro x Hin
  induction post <;>
    simp [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] at Hin ⊢ <;>
    try simp_all
  case app =>
    split at Hin
    · split at Hin <;>
        simp [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars] at Hin ⊢ <;>
        simp_all
    · simp [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars] at Hin ⊢
      simp_all
  all_goals grind