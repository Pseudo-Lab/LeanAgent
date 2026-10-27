by
  induction post
  case app fn e fn_ih e_ih =>
    intro a ha
    simp only [OldExpressions.substOld] at ha
    split at ha <;> try split at ha <;>
      simp_all [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars, List.Subset] <;>
      grind
  all_goals
    simp_all [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] <;>
    grind