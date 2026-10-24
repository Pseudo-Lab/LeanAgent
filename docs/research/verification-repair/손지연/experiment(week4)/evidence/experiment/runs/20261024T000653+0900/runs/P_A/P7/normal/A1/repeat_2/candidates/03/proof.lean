by
  generalize hΓ : [] = Γ at der
  have der' : Typing Γ t τ := der
  induction der <;> subst hΓ
  case var mem => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    rcases ih_l rfl l with val_l | ⟨t₁', red_l⟩
    · rcases ih_r rfl r with val_r | ⟨t₂', red_r⟩
      · obtain ⟨σ, u, hu⟩ := l.canonical_form_abs val_l
        exact Or.inr ⟨u ^ᵗᵗ t₂, by grind⟩
      · exact Or.inr ⟨t₁.app t₂', by grind⟩
    · exact Or.inr ⟨t₁'.app t₂, by grind⟩
  case tapp σ' der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · obtain ⟨_, u, hu⟩ := der.canonical_form_tabs val
      exact Or.inr ⟨u ^ᵗᵞ σ', by grind⟩
    · exact Or.inr ⟨.tapp t' σ', by grind⟩
  case let' t₁ σ t₂ τ L der _ ih _ =>
    rcases ih rfl der with val | ⟨t₁', red⟩
    · exact Or.inr ⟨t₂ ^ᵗᵗ t₁, by grind⟩
    · exact Or.inr ⟨t₁'.let' t₂, by grind⟩
  case inl der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · grind
    · exact Or.inr ⟨.inl t', by grind⟩
  case inr der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · grind
    · exact Or.inr ⟨.inr t', by grind⟩
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    rcases ih rfl der with val | ⟨t₁', red⟩
    · obtain ⟨u, hu | hu⟩ := der.canonical_form_sum val
      · exact Or.inr ⟨t₂ ^ᵗᵗ u, by grind⟩
      · exact Or.inr ⟨t₃ ^ᵗᵗ u, by grind⟩
    · exact Or.inr ⟨t₁'.case t₂ t₃, by grind⟩
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