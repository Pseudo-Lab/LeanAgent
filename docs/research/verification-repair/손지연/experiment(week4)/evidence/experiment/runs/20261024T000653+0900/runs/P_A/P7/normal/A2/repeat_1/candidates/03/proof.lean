by
  generalize eq : [] = Γ at der
  induction der <;> subst eq
  case var mem => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    right
    rcases ih_l rfl l with val_l | ⟨u, hu⟩
    · rcases ih_r rfl r with val_r | ⟨u, hu⟩
      · obtain ⟨_, u, _⟩ := l.canonical_form_abs val_l
        exact ⟨u ^ᵗᵗ t₂, by grind⟩
      · exact ⟨t₁.app u, by grind⟩
    · exact ⟨u.app t₂, by grind⟩
  case tapp σ' der _ ih =>
    right
    rcases ih rfl der with val | ⟨u, hu⟩
    · obtain ⟨_, u, _⟩ := der.canonical_form_tabs val
      exact ⟨u ^ᵗᵞ σ', by grind⟩
    · exact ⟨.tapp u σ', by grind⟩
  case let' t₁ σ t₂ τ L der _ ih _ =>
    right
    rcases ih rfl der with val | ⟨u, hu⟩
    · exact ⟨t₂ ^ᵗᵗ t₁, by grind⟩
    · exact ⟨u.let' t₂, by grind⟩
  case inl der _ ih =>
    rcases ih rfl der with val | ⟨u, hu⟩
    · grind
    · exact Or.inr ⟨.inl u, by grind⟩
  case inr der _ ih =>
    rcases ih rfl der with val | ⟨u, hu⟩
    · grind
    · exact Or.inr ⟨.inr u, by grind⟩
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    right
    rcases ih rfl der with val | ⟨u, hu⟩
    · have ⟨u, lr⟩ := der.canonical_form_sum val
      cases lr <;> [exact ⟨t₂ ^ᵗᵗ u, by grind⟩; exact ⟨t₃ ^ᵗᵗ u, by grind⟩]
    · exact ⟨u.case t₂ t₃, by grind⟩
  case sub => grind
  case abs σ _ τ L _ _ =>
    left
    exact ⟨LC.abs L (by grind only [→ wf, cases Term.LC]) (by grind only [→ wf])⟩
  case tabs L _ _ =>
    left
    exact ⟨LC.tabs L (by grind only [→ wf, cases Term.LC]) (by grind only [→ wf])⟩