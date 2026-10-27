by
  intros Hnorm
  induction post <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
          Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
  case app fn e fn_ih e_ih =>
    unfold extractOldExprVars
    split
    · simp [Lambda.LExpr.LExpr.getVars]
      intros x Hin
      exact Hin
    · next Hfalse =>
      cases Hnorm with
      | app H1 H2 Hn =>
        exfalso
        specialize Hn ?_
        constructor
        cases Hn
        apply Hfalse
        rfl
    · cases Hnorm with
      | app H1 H2 Hn =>
        apply List.Subset.app
        · exact List.Subset.trans (fn_ih H1) (by simp_all)
        · exact List.Subset.trans (e_ih H2) (by simp_all)
  all_goals
    cases Hnorm
    simp_all [List.Subset]