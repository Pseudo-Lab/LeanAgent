by
  generalize hΓ : ([] : Context Var) = Γ at der
  induction der <;>
    grind [cases Term.Value, cases Red, cases Typing, cases Sub]