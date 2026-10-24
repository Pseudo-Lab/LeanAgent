by
  intro x Hin
  induction post
  case app fn e fn_ih e_ih =>
    unfold OldExpressions.substOld at Hin
    split at Hin
    · split at Hin <;>
        simp_all [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars] <;>
        grind
    · simp_all [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars] <;>
      grind
  all_goals
    simp_all [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] <;>
    grind