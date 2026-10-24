by
  intro h
  induction h
  case app =>
    intro a ha
    unfold extractOldExprVars at ha
    split at ha <;>
      simp_all [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars] <;>
      grind
  all_goals
    simp_all [List.Subset, extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] <;>
    grind