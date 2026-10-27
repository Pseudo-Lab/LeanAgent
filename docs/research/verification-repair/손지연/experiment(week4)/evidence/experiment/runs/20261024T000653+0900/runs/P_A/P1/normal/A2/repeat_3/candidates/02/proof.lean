by
  induction post
  case app fn e fn_ih e_ih =>
    simp only [OldExpressions.substOld]
    split
    · split
      · simp [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars, List.Subset]
      · simp only [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars]
        exact List.subset_append_left
    · simp only [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars] at fn_ih e_ih ⊢
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp (fn_ih hx) with hx | hx
        · exact List.mem_append.mpr
            (Or.inl (List.mem_append.mpr (Or.inl hx)))
        · exact List.mem_append.mpr (Or.inr hx)
      · rcases List.mem_append.mp (e_ih hx) with hx | hx
        · exact List.mem_append.mpr
            (Or.inl (List.mem_append.mpr (Or.inr hx)))
        · exact List.mem_append.mpr (Or.inr hx)
  all_goals
    simp_all [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] <;>
    grind