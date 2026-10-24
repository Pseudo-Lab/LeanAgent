by
  generalize eq : [] = Γ at der
  have der' : Typing Γ t τ := der
  induction der <;> subst eq
  case var => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    rcases ih_l rfl l with val_l | ⟨t₁', red_l⟩
    · rcases ih_r rfl r with val_r | ⟨t₂', red_r⟩
      · obtain ⟨σ, u, eq⟩ := l.canonical_form_abs val_l
        grind
      · grind
    · grind
  case tapp σ' der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · obtain ⟨_, u, _⟩ := der.canonical_form_tabs val
      grind
    · grind
  case let' t₁ σ t₂ τ L der _ ih _ =>
    rcases ih rfl der with val | ⟨t₁', red⟩ <;> grind
  case inl der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩ <;> grind
  case inr der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩ <;> grind
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    rcases ih rfl der with val | ⟨t₁', red⟩
    · obtain ⟨u, lr⟩ := der.canonical_form_sum val
      cases lr <;> grind
    · grind
  case sub => grind
  case abs σ _ τ L _ _ =>
    left
    constructor
    apply LC.abs L
    · grind only [→ wf, cases Term.LC]
    · grind only [→ wf]
  case tabs L _ _ =>
    left
    constructor
    apply LC.tabs L
    · grind only [→ wf, cases Term.LC]
    · grind only [→ wf]