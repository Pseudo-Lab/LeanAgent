by
  intro Hnorm x Hin
  induction Hnorm <;>
    simp_all [OldExpressions.extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] <;>
    try grind
  case app fn e m Hnfn Hne Hwf ihfn ihe =>
    cases fn <;> cases e <;>
      simp_all [OldExpressions.extractOldExprVars,
        Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars] <;>
      grind