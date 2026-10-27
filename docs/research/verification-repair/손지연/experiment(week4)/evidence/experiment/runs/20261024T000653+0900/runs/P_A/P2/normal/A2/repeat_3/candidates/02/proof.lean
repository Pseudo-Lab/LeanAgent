by
  intros Hnorm
  have append_mono {a b c d : List Expression.Ident}
      (hab : a.Subset b) (hcd : c.Subset d) :
      (a ++ c).Subset (b ++ d) :=
    List.append_subset.mpr ⟨
      List.Subset.trans hab List.subset_append_left,
      List.subset_append_of_subset_right hcd⟩
  induction post <;>
    simp [Imperative.HasVarsPure.getVars, extractOldExprVars,
          Lambda.LExpr.LExpr.getVars] at * <;>
    try simp_all
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
        specialize Hn ?_
        constructor
        cases Hn
        apply Hfalse
        rfl
    · cases Hnorm with
      | app H1 H2 Hn =>
        apply append_mono
        · exact fn_ih H1
        · exact e_ih H2
  case abs ih =>
    cases Hnorm
    apply ih <;> assumption
  case quant trih eih =>
    cases Hnorm
    apply append_mono
    · apply trih <;> assumption
    · apply eih <;> assumption
  case ite cih tih eih =>
    cases Hnorm
    apply append_mono
    · apply cih <;> assumption
    · apply append_mono
      · apply tih <;> assumption
      · apply eih <;> assumption
  case eq ih1 ih2 =>
    cases Hnorm
    apply append_mono
    · apply ih1 <;> assumption
    · apply ih2 <;> assumption