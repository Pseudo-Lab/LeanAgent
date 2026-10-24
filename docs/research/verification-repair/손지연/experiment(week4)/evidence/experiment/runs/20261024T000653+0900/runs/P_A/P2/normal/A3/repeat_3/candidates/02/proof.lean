by
  intro Hnorm
  have append_mono {a b c d : List Expression.Ident}
      (hac : a.Subset c) (hbd : b.Subset d) :
      (a ++ b).Subset (c ++ d) := by
    intro x hx
    simp only [List.mem_append] at hx ⊢
    exact hx.imp hac hbd
  induction Hnorm
  case app fn e m Hnfn Hne Hwf ih1 ih2 =>
    unfold extractOldExprVars
    split
    · simp [Lambda.LExpr.LExpr.getVars]
      intro x hx
      exact hx
    · next Hfalse =>
      exfalso
      specialize Hwf (by constructor)
      cases Hwf
      exact Hfalse rfl
    · simpa [Lambda.LExpr.LExpr.getVars] using append_mono ih1 ih2
  case quant tr e trih eih =>
    simpa [extractOldExprVars, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] using append_mono trih eih
  case ite c t e cih tih eih =>
    simpa [extractOldExprVars, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] using append_mono cih (append_mono tih eih)
  case eq e1 e2 e1ih e2ih =>
    simpa [extractOldExprVars, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] using append_mono e1ih e2ih
  all_goals
    simp [extractOldExprVars, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] at *