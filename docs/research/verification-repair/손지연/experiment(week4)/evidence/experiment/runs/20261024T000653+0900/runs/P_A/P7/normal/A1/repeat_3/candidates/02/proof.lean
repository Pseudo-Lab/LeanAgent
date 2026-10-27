by
  generalize eq : [] = Γ at der
  have der' : Typing Γ t τ := der
  induction der <;> subst eq
  case var mem => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    right
    rcases ih_l rfl l with val_l | ⟨t₁', red_l⟩
    · rcases ih_r rfl r with val_r | ⟨t₂', red_r⟩
      · obtain ⟨σ, body, h⟩ := l.canonical_form_abs val_l
        exact ⟨body ^ᵗᵗ t₂, by grind⟩
      · exact ⟨t₁.app t₂', Red.appᵣ val_l red_r⟩
    · exact ⟨t₁'.app t₂, Red.appₗ red_l⟩
  case tapp σ' der _ ih =>
    right
    rcases ih rfl der with val | ⟨t', red⟩
    · obtain ⟨_, body, h⟩ := der.canonical_form_tabs val
      exact ⟨body ^ᵗᵞ σ', by grind⟩
    · exact ⟨.tapp t' σ', Red.tapp red⟩
  case let' t₁ σ t₂ τ L der _ ih _ =>
    right
    rcases ih rfl der with val | ⟨t₁', red⟩
    · exact ⟨t₂ ^ᵗᵗ t₁, by grind⟩
    · exact ⟨t₁'.let' t₂, Red.let_bind red⟩
  case inl der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · left
      grind
    · exact Or.inr ⟨.inl t', Red.inl red⟩
  case inr der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · left
      grind
    · exact Or.inr ⟨.inr t', Red.inr red⟩
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    right
    rcases ih rfl der with val | ⟨t₁', red⟩
    · obtain ⟨u, h | h⟩ := der.canonical_form_sum val
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