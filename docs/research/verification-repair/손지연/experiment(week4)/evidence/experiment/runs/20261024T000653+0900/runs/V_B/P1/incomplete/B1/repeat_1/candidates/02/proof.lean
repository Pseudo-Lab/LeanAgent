by
  intro x Hin
  induction post <;>
    simp [OldExpressions.substOld,
      Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] at * <;>
    (try split at *) <;>
    (try split at *)
  case fvar =>
    exact Or.inl Hin
  all_goals simp_all