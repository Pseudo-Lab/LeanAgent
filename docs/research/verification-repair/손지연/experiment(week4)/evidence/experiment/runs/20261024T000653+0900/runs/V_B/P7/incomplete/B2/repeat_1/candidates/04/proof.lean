by
  generalize hΓ : ([] : Context Var (Ty Var)) = Γ
  rw [hΓ] at der
  induction der <;>
    grind [cases Term.Value, cases Red, cases Typing, cases Sub]