by
  generalize eq : [] = Γ at der
  have der' := der
  induction der <;> subst eq
  case var => grind
  case app t₁ _ _ t₂ l r il ir =>
    right
    rcases il rfl l with vl | ⟨t₁', h₁⟩
    · rcases ir rfl r with vr | ⟨t₂', h₂⟩
      · obtain ⟨_, u, rfl⟩ := l.canonical_form_abs vl
        exact ⟨u ^ᵗᵗ t₂, by grind⟩
      · exact ⟨t₁.app t₂', by grind⟩
    · exact ⟨t₁'.app t₂, by grind⟩
  case tapp σ' der _ ih =>
    right
    rcases ih rfl der with v | ⟨t', h⟩
    · obtain ⟨_, u, rfl⟩ := der.canonical_form_tabs v
      exact ⟨u ^ᵗᵞ σ', by grind⟩
    · exact ⟨.tapp t' σ', by grind⟩
  case let' t₁ _ t₂ _ _ der _ ih _ =>
    right
    rcases ih rfl der with v | ⟨t₁', h⟩
    · exact ⟨t₂ ^ᵗᵗ t₁, by grind⟩
    · exact ⟨t₁'.let' t₂, by grind⟩
  case inl der _ ih | inr der _ ih =>
    rcases ih rfl der with v | ⟨t', h⟩
    · grind
    · first
      | exact .inr ⟨.inl t', by grind⟩
      | exact .inr ⟨.inr t', by grind⟩
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    right
    rcases ih rfl der with v | ⟨t₁', h⟩
    · obtain ⟨u, rfl | rfl⟩ := der.canonical_form_sum v
      · exact ⟨t₂ ^ᵗᵗ u, by grind⟩
      · exact ⟨t₃ ^ᵗᵗ u, by grind⟩
    · exact ⟨t₁'.case t₂ t₃, by grind⟩
  case sub => grind
  case abs _ _ _ L _ _ | tabs L _ _ =>
    left
    constructor
    first | apply LC.abs L | apply LC.tabs L
    all_goals grind only [→ wf, cases Term.LC]