by
  intro h
  induction h
  case app fn e m hfn he hold ihfn ihe =>
    intro a ha
    unfold extractOldExprVars at ha
    split at ha <;>
      simp_all [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars] <;>
      try solve_by_elim [ihfn, ihe]
    all_goals
      cases hold (by constructor)
      simp_all
  all_goals
    simp_all [List.Subset, extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] <;>
    solve_by_elim