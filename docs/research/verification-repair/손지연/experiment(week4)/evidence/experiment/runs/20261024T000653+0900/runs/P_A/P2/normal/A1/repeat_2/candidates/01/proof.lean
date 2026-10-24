by
  intro Hnorm
  have append_mono {a b c d : List Expression.Ident}
      (hac : a.Subset c) (hbd : b.Subset d) :
      (a ++ b).Subset (c ++ d) := by
    intro x hx
    simp only [List.mem_append] at hx ⊢
    exact hx.elim (fun h => Or.inl (hac h)) (fun h => Or.inr (hbd h))
  induction post <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
          Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
  case app fn e fn_ih e_ih =>
    unfold extractOldExprVars
    split
    · simp [Lambda.LExpr.LExpr.getVars]
    · next Hfalse =>
      cases Hnorm with
      | app H1 H2 Hn =>
        exfalso
        specialize Hn (by
          constructor
          cases Hn
          apply Hfalse
          rfl)
        exact Hn
    · cases Hnorm with
      | app H1 H2 Hn =>
        exact append_mono (fn_ih H1) (e_ih H2)
  case abs ih =>
    cases Hnorm
    apply ih
    assumption
  case quant trih eih =>
    cases Hnorm
    apply append_mono
    · apply trih
      assumption
    · apply eih
      assumption
  case ite cih tih eih =>
    cases Hnorm
    apply append_mono
    · apply cih
      assumption
    · apply append_mono
      · apply tih
        assumption
      · apply eih
        assumption
  case eq ih1 ih2 =>
    cases Hnorm
    apply append_mono
    · apply ih1
      assumption
    · apply ih2
      assumption