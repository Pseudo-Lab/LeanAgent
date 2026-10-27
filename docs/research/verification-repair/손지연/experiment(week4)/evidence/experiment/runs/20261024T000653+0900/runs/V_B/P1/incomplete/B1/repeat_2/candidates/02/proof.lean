by
  intro v Hin
  induction post <;>
    simp [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] at *
  case app fn e fn_ih e_ih =>
    split at Hin
    · split at Hin <;>
        simp_all [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars]
    · simp [Imperative.HasVarsPure.getVars,
          Lambda.LExpr.LExpr.getVars] at Hin ⊢
      rcases Hin with Hin | Hin
      · rcases fn_ih Hin with Hin | Hin
        · exact Or.inl (Or.inl Hin)
        · exact Or.inr Hin
      · rcases e_ih Hin with Hin | Hin
        · exact Or.inl (Or.inr Hin)
        · exact Or.inr Hin
  all_goals grind