by
  generalize eq : [] = Γ at der
  have der' : Typing Γ t τ := der
  induction der <;> subst eq
  case var => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    right
    obtain val_l | ⟨t₁', red_l⟩ := ih_l rfl l
    · obtain val_r | ⟨t₂', red_r⟩ := ih_r rfl r
      · obtain ⟨_, body, h⟩ := l.canonical_form_abs val_l
        exact ⟨body ^ᵗᵗ t₂, by grind⟩
      · exact ⟨t₁.app t₂', by grind⟩
    · exact ⟨t₁'.app t₂, by grind⟩
  case tapp σ' der _ ih =>
    right
    obtain val | ⟨t', red⟩ := ih rfl der
    · obtain ⟨_, body, h⟩ := der.canonical_form_tabs val
      exact ⟨body ^ᵗᵞ σ', by grind⟩
    · exact ⟨.tapp t' σ', by grind⟩
  case let' t₁ σ t₂ τ L der _ ih _ =>
    right
    obtain val | ⟨t₁', red⟩ := ih rfl der
    · exact ⟨t₂ ^ᵗᵗ t₁, by grind⟩
    · exact ⟨t₁'.let' t₂, by grind⟩
  case inl der _ ih =>
    obtain val | ⟨t', red⟩ := ih rfl der
    · grind
    · exact Or.inr ⟨.inl t', by grind⟩
  case inr der _ ih =>
    obtain val | ⟨t', red⟩ := ih rfl der
    · grind
    · exact Or.inr ⟨.inr t', by grind⟩
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    right
    obtain val | ⟨t₁', red⟩ := ih rfl der
    · obtain ⟨u, lr⟩ := der.canonical_form_sum val
      cases lr
      · exact ⟨t₂ ^ᵗᵗ u, by grind⟩
      · exact ⟨t₃ ^ᵗᵗ u, by grind⟩
    · exact ⟨t₁'.case t₂ t₃, by grind⟩
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