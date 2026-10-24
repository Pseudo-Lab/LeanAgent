by
  generalize hΓ : [] = Γ at der
  induction der <;>
    grind [cases Term.Value, cases Typing, cases Sub, cases Red]