by
  intro Hnorm
  have append_subset {a b c d : List Expression.Ident}
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
    cases Hnorm with
    | app hfn he hnold =>
      unfold extractOldExprVars
      split
      · simp [Lambda.LExpr.LExpr.getVars]
        intro x hx
        exact hx
      · rename_i hfalse
        exfalso
        specialize hnold ?_
        constructor
        cases hnold
        apply hfalse
        rfl
      · exact append_subset (fn_ih hfn) (e_ih he)
  case abs ih =>
    cases Hnorm with
    | abs he => exact ih he
  case quant trih eih =>
    cases Hnorm with
    | quant ht he => exact append_subset (trih ht) (eih he)
  case ite cih tih eih =>
    cases Hnorm with
    | ite hc ht he =>
      exact append_subset (cih hc) (append_subset (tih ht) (eih he))
  case eq ih1 ih2 =>
    cases Hnorm with
    | eq h1 h2 => exact append_subset (ih1 h1) (ih2 h2)