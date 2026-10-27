by
  intro Hnorm
  have appendSubset : ∀ {a b c d : List Expression.Ident},
      a.Subset c → b.Subset d → (a ++ b).Subset (c ++ d) := by
    intro a b c d ha hb x hx
    simp_all
  induction post <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
      Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
  case app fn e fn_ih e_ih =>
    unfold extractOldExprVars
    split
    · simp [Lambda.LExpr.LExpr.getVars]
    · rename_i Hfalse
      cases Hnorm with
      | app Hfn He Hshape =>
        exfalso
        specialize Hshape (by constructor)
        cases Hshape
        exact Hfalse rfl
    · cases Hnorm with
      | app Hfn He Hshape =>
        exact appendSubset (fn_ih Hfn) (e_ih He)
  case abs ih =>
    cases Hnorm with
    | abs H => exact ih H
  case quant tr_ih e_ih =>
    cases Hnorm with
    | quant Htr He => exact appendSubset (tr_ih Htr) (e_ih He)
  case ite c_ih t_ih e_ih =>
    cases Hnorm with
    | ite Hc Ht He =>
      exact appendSubset (c_ih Hc) (appendSubset (t_ih Ht) (e_ih He))
  case eq e1_ih e2_ih =>
    cases Hnorm with
    | eq H1 H2 => exact appendSubset (e1_ih H1) (e2_ih H2)