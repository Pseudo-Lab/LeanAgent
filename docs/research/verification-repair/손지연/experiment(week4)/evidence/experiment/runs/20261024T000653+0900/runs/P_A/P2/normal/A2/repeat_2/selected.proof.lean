by
  intros Hnorm
  induction post <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
          Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
  all_goals
    have appendSubset {a b c d : List Expression.Ident}
        (h₁ : a.Subset b) (h₂ : c.Subset d) :
        (a ++ c).Subset (b ++ d) := by
      intro x hx
      simp only [List.mem_append] at hx ⊢
      cases hx with
      | inl hx => exact Or.inl (h₁ hx)
      | inr hx => exact Or.inr (h₂ hx)
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
        exact appendSubset (fn_ih H1) (e_ih H2)
  case abs ih =>
    cases Hnorm
    apply ih <;> assumption
  case quant trih eih =>
    cases Hnorm
    exact appendSubset (trih (by assumption)) (eih (by assumption))
  case ite cih tih eih =>
    cases Hnorm
    exact appendSubset (cih (by assumption))
      (appendSubset (tih (by assumption)) (eih (by assumption)))
  case eq ih1 ih2 =>
    cases Hnorm
    exact appendSubset (ih1 (by assumption)) (ih2 (by assumption))