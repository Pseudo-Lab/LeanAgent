by
  generalize eq : [] = Γ at der
  have der' : Typing Γ t τ := der
  induction der <;> subst eq
  case var mem => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    rcases ih_l rfl l with val_l | ⟨t₁', red_l⟩
    · rcases ih_r rfl r with val_r | ⟨t₂', red_r⟩
      · obtain ⟨σ, body, h⟩ := l.canonical_form_abs val_l
        exact .inr ⟨body ^ᵗᵗ t₂, by grind⟩
      · exact .inr ⟨t₁.app t₂', by grind⟩
    · exact .inr ⟨t₁'.app t₂, by grind⟩
  case tapp σ' der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · obtain ⟨σ, body, h⟩ := der.canonical_form_tabs val
      exact .inr ⟨body ^ᵗᵞ σ', by grind⟩
    · exact .inr ⟨.tapp t' σ', by grind⟩
  case let' t₁ σ t₂ τ L der _ ih _ =>
    rcases ih rfl der with val | ⟨t₁', red⟩
    · exact .inr ⟨t₂ ^ᵗᵗ t₁, by grind⟩
    · exact .inr ⟨t₁'.let' t₂, by grind⟩
  case inl der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · exact .inl (by grind)
    · exact .inr ⟨.inl t', by grind⟩
  case inr der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · exact .inl (by grind)
    · exact .inr ⟨.inr t', by grind⟩
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    rcases ih rfl der with val | ⟨t₁', red⟩
    · have ⟨u, lr⟩ := der.canonical_form_sum val
      cases lr <;> [exact .inr ⟨t₂ ^ᵗᵗ u, by grind⟩; exact .inr ⟨t₃ ^ᵗᵗ u, by grind⟩]
    · exact .inr ⟨t₁'.case t₂ t₃, by grind⟩
  case sub => grind
  case abs σ _ τ L _ _ =>
    exact .inl (Term.Value.abs (LC.abs L (by grind only [→ wf, cases Term.LC]) (by grind only [→ wf])))
  case tabs L _ _ =>
    exact .inl (Term.Value.tabs (LC.tabs L (by grind only [→ wf, cases Term.LC]) (by grind only [→ wf])))