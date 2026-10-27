by
  generalize h : [] = Γ at der
  induction der <;> subst h
  case var mem => grind
  case app t₁ _ _ t₂ l r il ir =>
    right
    obtain vl | ⟨u, hu⟩ := il rfl
    · obtain vr | ⟨v, hv⟩ := ir rfl
      · obtain ⟨_, b, hb⟩ := l.canonical_form_abs vl
        exact ⟨b ^ᵗᵗ t₂, by grind⟩
      · exact ⟨t₁.app v, by grind⟩
    · exact ⟨u.app t₂, by grind⟩
  case tapp σ' der _ ih =>
    right
    obtain val | ⟨u, hu⟩ := ih rfl
    · obtain ⟨_, b, hb⟩ := der.canonical_form_tabs val
      exact ⟨b ^ᵗᵞ σ', by grind⟩
    · exact ⟨.tapp u σ', by grind⟩
  case let' t₁ σ t₂ τ L der _ ih _ =>
    right
    obtain val | ⟨u, hu⟩ := ih rfl
    · exact ⟨t₂ ^ᵗᵗ t₁, by grind⟩
    · exact ⟨u.let' t₂, by grind⟩
  case inl der _ ih =>
    obtain val | ⟨u, hu⟩ := ih rfl
    · grind
    · exact Or.inr ⟨.inl u, by grind⟩
  case inr der _ ih =>
    obtain val | ⟨u, hu⟩ := ih rfl
    · grind
    · exact Or.inr ⟨.inr u, by grind⟩
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    right
    obtain val | ⟨u, hu⟩ := ih rfl
    · obtain ⟨v, lr⟩ := der.canonical_form_sum val
      cases lr <;> [exact ⟨t₂ ^ᵗᵗ v, by grind⟩; exact ⟨t₃ ^ᵗᵗ v, by grind⟩]
    · exact ⟨u.case t₂ t₃, by grind⟩
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