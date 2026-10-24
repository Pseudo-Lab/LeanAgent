by
  intro x hx
  induction post generalizing x <;>
    simp [substOld, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars] at hx ⊢ <;>
    (try split at hx ⊢) <;>
    (try split at hx ⊢) <;>
    simp_all