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
        specialize Hn (by constructor)
        cases Hn
        apply Hfalse
        rfl
    · cases Hnorm with
      | app H1 H2 Hn =>
        exact List.Subset.app (fn_ih H1) (e_ih H2)
  case abs ih =>
    cases Hnorm
    apply ih <;> assumption
  case quant trih eih =>
    cases Hnorm
    exact List.Subset.app (trih (by assumption)) (eih (by assumption))
  case ite cih tih eih =>
    cases Hnorm
    exact List.Subset.app (cih (by assumption))
      (List.Subset.app (tih (by assumption)) (eih (by assumption)))
  case eq ih1 ih2 =>
    cases Hnorm
    exact List.Subset.app (ih1 (by assumption)) (ih2 (by assumption))