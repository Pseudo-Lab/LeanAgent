by
  intro Hnorm
  induction Hnorm
  case app fn e m Hnfn Hne Hwf ihfn ihe =>
    by_cases Hold : IsOldPred fn
    · have Hfv := Hwf Hold
      cases Hold
      cases Hfv
      intro a Hin
      unfold extractOldExprVars at Hin
      simpa [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars] using Hin
    · intro a Hin
      cases fn <;> cases e <;>
        simp_all [extractOldExprVars,
          Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars,
          List.Subset] <;>
        grind
  all_goals
    simp_all [extractOldExprVars,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars,
      List.Subset] <;>
    grind