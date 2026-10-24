by
  induction post
  case app fn e fn_ih e_ih =>
    intro a ha
    simp only [OldExpressions.substOld] at ha
    split at ha <;> try split at ha <;>
      simp_all [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars, List.Subset] <;>
      grind
    change a ∈
      (Imperative.HasVarsPure.getVars
          (OldExpressions.substOld h2 (Lambda.LExpr.fvar m h1 ty) fn) ++
       Imperative.HasVarsPure.getVars
          (OldExpressions.substOld h2 (Lambda.LExpr.fvar m h1 ty) e)) at ha
    change a ∈
      (Imperative.HasVarsPure.getVars fn ++
       Imperative.HasVarsPure.getVars e) ++ [h1]
    simp only [List.mem_append, List.mem_singleton] at ha ⊢
    rcases ha with ha | ha
    · have h := fn_ih ha
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · have h := e_ih ha
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  all_goals
    simp_all [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.Subset] <;>
    grind