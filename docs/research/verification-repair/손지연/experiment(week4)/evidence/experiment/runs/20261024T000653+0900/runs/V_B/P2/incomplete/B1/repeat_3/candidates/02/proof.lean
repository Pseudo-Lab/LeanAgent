by
  intro Hnorm
  induction Hnorm
  case app fn e m Hnfn Hne Hwf ihfn ihe =>
    cases fn <;> cases e <;>
      simp_all [extractOldExprVars,
        Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars,
        CoreIdent.unres] <;>
      (try split) <;>
      simp_all [extractOldExprVars,
        Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars,
        CoreIdent.unres] <;>
      (try split) <;>
      simp_all [extractOldExprVars,
        Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars,
        CoreIdent.unres] <;>
      (try split) <;>
      simp_all [extractOldExprVars,
        Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars,
        CoreIdent.unres] <;>
      grind
  all_goals
    simp_all [extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars,
      List.Subset] <;>
    grind