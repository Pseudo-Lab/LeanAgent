by
  intro Hnorm
  have appendSubset {a b c d : List Expression.Ident}
      (hab : a.Subset b) (hcd : c.Subset d) :
      (a ++ c).Subset (b ++ d) := by
    intro x hx
    simp only [List.mem_append] at hx ⊢
    exact hx.elim (fun h => Or.inl (hab h)) (fun h => Or.inr (hcd h))
  induction post
  case const =>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
      Lambda.LExpr.LExpr.getVars]
  case op =>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
      Lambda.LExpr.LExpr.getVars]
  case bvar =>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
      Lambda.LExpr.LExpr.getVars]
  case fvar =>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
      Lambda.LExpr.LExpr.getVars]
  case abs ih =>
    cases Hnorm with
    | abs H =>
      simpa only [Imperative.HasVarsPure.getVars, extractOldExprVars,
        Lambda.LExpr.LExpr.getVars] using ih H
  case quant trih eih =>
    cases Hnorm with
    | quant Ht He =>
      simpa only [Imperative.HasVarsPure.getVars, extractOldExprVars,
        Lambda.LExpr.LExpr.getVars] using appendSubset (trih Ht) (eih He)
  case app fn e fn_ih e_ih =>
    unfold extractOldExprVars
    split
    · simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars]
      intro x hx
      exact hx
    · next Hfalse =>
      cases Hnorm with
      | app H1 H2 Hn =>
        exfalso
        specialize Hn (by constructor)
        cases Hn
        exact Hfalse rfl
    · cases Hnorm with
      | app H1 H2 Hn =>
        simpa only [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars] using
          appendSubset (fn_ih H1) (e_ih H2)
  case ite cih tih eih =>
    cases Hnorm with
    | ite Hc Ht He =>
      simpa only [Imperative.HasVarsPure.getVars, extractOldExprVars,
        Lambda.LExpr.LExpr.getVars] using
          appendSubset (cih Hc) (appendSubset (tih Ht) (eih He))
  case eq e1ih e2ih =>
    cases Hnorm with
    | eq H1 H2 =>
      simpa only [Imperative.HasVarsPure.getVars, extractOldExprVars,
        Lambda.LExpr.LExpr.getVars] using appendSubset (e1ih H1) (e2ih H2)