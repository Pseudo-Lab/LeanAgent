by
  have appendSubset :
      ∀ {a b c d : List Expression.Ident},
        a.Subset (c ++ [h1]) →
        b.Subset (d ++ [h1]) →
        (a ++ b).Subset (c ++ d ++ [h1]) := by
    intro a b c d hac hbd x hx
    simp only [List.mem_append, List.mem_singleton] at hx hac hbd ⊢
    rcases hx with hx | hx
    · rcases hac hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
    · rcases hbd hx with hx | hx
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
  induction post with
  | const c =>
      simp [List.Subset, substOld, Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars]
  | op o ty =>
      simp [List.Subset, substOld, Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars]
  | bvar b =>
      simp [List.Subset, substOld, Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars]
  | fvar md name ty =>
      simp [List.Subset, substOld, Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars]
  | abs md ty e ih =>
      simpa [substOld, Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars] using ih
  | quant md k ty tr e trih eih =>
      simpa [substOld, Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars, List.append_assoc] using
        appendSubset trih eih
  | app md fn e fnih eih =>
      simp only [substOld]
      split
      · split <;>
          simp_all [List.Subset, Imperative.HasVarsPure.getVars,
            Lambda.LExpr.LExpr.getVars]
      · simpa [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars, List.append_assoc] using
          appendSubset fnih eih
  | ite md c t e cih tih eih =>
      simpa [substOld, Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars, List.append_assoc] using
        appendSubset (appendSubset cih tih) eih
  | eq md e₁ e₂ e₁ih e₂ih =>
      simpa [substOld, Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars, List.append_assoc] using
        appendSubset e₁ih e₂ih