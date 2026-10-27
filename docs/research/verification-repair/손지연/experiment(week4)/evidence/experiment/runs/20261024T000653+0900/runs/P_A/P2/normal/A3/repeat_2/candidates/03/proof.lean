by
  intro Hnorm
  have app {a b c d : List Expression.Ident}
      (hab : a.Subset b) (hcd : c.Subset d) :
      (a ++ c).Subset (b ++ d) := by
    intro x hx
    simp only [List.mem_append] at hx ⊢
    exact hx.elim (fun h => Or.inl (hab h)) (fun h => Or.inr (hcd h))
  induction Hnorm
  case app fn e m Hfn He Hbad ihfn ihe =>
    unfold extractOldExprVars
    split
    · simp [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars, List.Subset]
    · next Hfalse =>
      exfalso
      specialize Hbad (by constructor)
      cases Hbad
      exact Hfalse () _ _ rfl
    · simpa only [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars] using app ihfn ihe
  all_goals
    simp_all only [Imperative.HasVarsPure.getVars, extractOldExprVars,
      Lambda.LExpr.LExpr.getVars, List.Subset]