by
  intro Hnorm
  have append_mono {a b c d : List Expression.Ident}
      (hac : a.Subset c) (hbd : b.Subset d) :
      (a ++ b).Subset (c ++ d) := by
    intro x hx
    simp only [List.mem_append] at hx ⊢
    exact hx.elim (fun ha => Or.inl (hac ha)) (fun hb => Or.inr (hbd hb))
  induction post <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
          Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
  case app fn e fn_ih e_ih =>
    unfold extractOldExprVars
    split
    · simp [Lambda.LExpr.LExpr.getVars]
      intro x Hin
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
        exact append_mono (fn_ih H1) (e_ih H2)
  case abs ih =>
    cases Hnorm
    apply ih <;> assumption
  case quant trih eih =>
    cases Hnorm
    exact append_mono (trih (by assumption)) (eih (by assumption))
  case ite cih tih eih =>
    cases Hnorm
    exact append_mono (cih (by assumption))
      (append_mono (tih (by assumption)) (eih (by assumption)))
  case eq ih1 ih2 =>
    cases Hnorm
    exact append_mono (ih1 (by assumption)) (ih2 (by assumption))