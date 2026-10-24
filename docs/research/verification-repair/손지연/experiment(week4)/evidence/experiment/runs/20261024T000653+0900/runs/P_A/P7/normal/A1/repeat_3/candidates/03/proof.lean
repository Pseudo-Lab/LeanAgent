by
  generalize hΓ : [] = Γ at der
  have der' : Typing Γ t τ := der
  induction der <;> subst hΓ
  case var mem => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    right
    rcases ih_l rfl l with val_l | ⟨t₁', step_l⟩
    · rcases ih_r rfl r with val_r | ⟨t₂', step_r⟩
      · obtain ⟨σ, body, h⟩ := l.canonical_form_abs val_l
        exact ⟨body ^ᵗᵗ t₂, by grind⟩
      · exact ⟨t₁.app t₂', by grind⟩
    · exact ⟨t₁'.app t₂, by grind⟩
  case tapp σ' der _ ih =>
    right
    rcases ih rfl der with val | ⟨t', step⟩
    · obtain ⟨σ, body, h⟩ := der.canonical_form_tabs val
      exact ⟨body ^ᵗᵞ σ', by grind⟩
    · exact ⟨.tapp t' σ', by grind⟩
  case let' t₁ σ t₂ τ L der _ ih _ =>
    right
    rcases ih rfl der with val | ⟨t₁', step⟩
    · exact ⟨t₂ ^ᵗᵗ t₁, by grind⟩
    · exact ⟨t₁'.let' t₂, by grind⟩
  case inl der _ ih =>
    rcases ih rfl der with val | ⟨t', step⟩
    · grind
    · exact Or.inr ⟨.inl t', by grind⟩
  case inr der _ ih =>
    rcases ih rfl der with val | ⟨t', step⟩
    · grind
    · exact Or.inr ⟨.inr t', by grind⟩
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    right
    rcases ih rfl der with val | ⟨t₁', step⟩
    · obtain ⟨arg, side⟩ := der.canonical_form_sum val
      rcases side with h | h
      · exact ⟨t₂ ^ᵗᵗ arg, by grind⟩
      · exact ⟨t₃ ^ᵗᵗ arg, by grind⟩
    · exact ⟨t₁'.case t₂ t₃, by grind⟩
  case sub => grind
  case abs σ _ τ L _ _ =>
    exact Or.inl ⟨LC.abs L (by grind only [→ wf, cases Term.LC]) (by grind only [→ wf])⟩
  case tabs L _ _ =>
    exact Or.inl ⟨LC.tabs L (by grind only [→ wf, cases Term.LC]) (by grind only [→ wf])⟩