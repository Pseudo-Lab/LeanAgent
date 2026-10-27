by
  revert der
  generalize hΓ : ([] : Context Var (Ty Var)) = Γ
  intro der
  induction der <;> grind [cases Term.Value, cases Red]