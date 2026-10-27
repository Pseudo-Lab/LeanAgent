by
  intro x Hin
  induction post <;>
    simp [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] at * <;> try simp_all
  case app fn e fn_ih e_ih =>
    split at Hin
    · split at Hin <;>
        simp_all [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars]
    · simp [Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars] at Hin
      rcases Hin with Hin | Hin
      · rcases fn_ih Hin with Hin | Hin
        · exact Or.inl Hin
        · exact Or.inr (Or.inr Hin)
      · rcases e_ih Hin with Hin | Hin
        · exact Or.inr (Or.inl Hin)
        · exact Or.inr (Or.inr Hin)
  case quant k ty tr_ih e_ih =>
    rcases Hin with Hin | Hin
    · rcases tr_ih Hin with Hin | Hin
      · exact Or.inl Hin
      · exact Or.inr (Or.inr Hin)
    · rcases e_ih Hin with Hin | Hin
      · exact Or.inr (Or.inl Hin)
      · exact Or.inr (Or.inr Hin)
  case ite c t e c_ih t_ih e_ih =>
    rcases Hin with Hin | Hin | Hin
    · rcases c_ih Hin with Hin | Hin
      · exact Or.inl Hin
      · exact Or.inr (Or.inr (Or.inr Hin))
    · rcases t_ih Hin with Hin | Hin
      · exact Or.inr (Or.inl Hin)
      · exact Or.inr (Or.inr (Or.inr Hin))
    · rcases e_ih Hin with Hin | Hin
      · exact Or.inr (Or.inr (Or.inl Hin))
      · exact Or.inr (Or.inr (Or.inr Hin))
  case eq e1 e2 e1_ih e2_ih =>
    rcases Hin with Hin | Hin
    · rcases e1_ih Hin with Hin | Hin
      · exact Or.inl Hin
      · exact Or.inr (Or.inr Hin)
    · rcases e2_ih Hin with Hin | Hin
      · exact Or.inr (Or.inl Hin)
      · exact Or.inr (Or.inr Hin)