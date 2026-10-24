by
  generalize eq : [] = Γ at der
  have der' : Typing Γ t τ := der
  induction der <;> subst eq
  case var mem => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    right
    rcases ih_l rfl l with val_l | ⟨t₁', red_l⟩
    · rcases ih_r rfl r with val_r | ⟨t₂', red_r⟩
      · obtain ⟨σ, u, eq⟩ := l.canonical_form_abs val_l
        exists u ^ᵗᵗ t₂
        grind
      · exists t₁.app t₂'
        grind
    · exists t₁'.app t₂
      grind
  case tapp σ' der _ ih =>
    right
    rcases ih rfl der with val | ⟨t', red⟩
    · obtain ⟨_, u, _⟩ := der.canonical_form_tabs val
      exists u ^ᵗᵞ σ'
      grind
    · exists .tapp t' σ'
      grind
  case let' t₁ σ t₂ τ L der _ ih _ =>
    right
    rcases ih rfl der with val | ⟨t₁', red⟩
    · exists t₂ ^ᵗᵗ t₁
      grind
    · exists t₁'.let' t₂
      grind
  case inl der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · grind
    · right
      exists .inl t'
      grind
  case inr der _ ih =>
    rcases ih rfl der with val | ⟨t', red⟩
    · grind
    · right
      exists .inr t'
      grind
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    right
    rcases ih rfl der with val | ⟨t₁', red⟩
    · obtain ⟨u, lr⟩ := der.canonical_form_sum val
      cases lr <;> [exists t₂ ^ᵗᵗ u; exists t₃ ^ᵗᵗ u] <;> grind
    · exists t₁'.case t₂ t₃
      grind
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