by
  generalize eq : [] = Γ at der
  induction der <;> subst eq
  case var mem => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    right
    cases ih_l rfl with
    | inl val_l =>
        cases ih_r rfl with
        | inl val_r =>
            have ⟨σ, t₁, eq⟩ := l.canonical_form_abs val_l
            exists t₁ ^ᵗᵗ t₂
            grind
        | inr red_r =>
            obtain ⟨t₂', _⟩ := red_r
            exists t₁.app t₂'
            grind
    | inr red_l =>
        obtain ⟨t₁', _⟩ := red_l
        exists t₁'.app t₂
        grind
  case tapp σ' der _ ih =>
    right
    specialize ih rfl
    cases ih with
    | inl val =>
        obtain ⟨_, t, _⟩ := der.canonical_form_tabs val
        exists t ^ᵗᵞ σ'
        grind
    | inr red =>
        obtain ⟨t', _⟩ := red
        exists .tapp t' σ'
        grind
  case let' t₁ σ t₂ τ L der _ ih _ =>
    right
    cases ih rfl with
    | inl _ =>
        exists t₂ ^ᵗᵗ t₁
        grind
    | inr red =>
        obtain ⟨t₁', _⟩ := red
        exists t₁'.let' t₂
        grind
  case inl der _ ih =>
    cases ih rfl with
    | inl val => grind
    | inr red =>
        right
        obtain ⟨t', _⟩ := red
        exists .inl t'
        grind
  case inr der _ ih =>
    cases ih rfl with
    | inl val => grind
    | inr red =>
        right
        obtain ⟨t', _⟩ := red
        exists .inr t'
        grind
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    right
    cases ih rfl with
    | inl val =>
        have ⟨t₁, lr⟩ := der.canonical_form_sum val
        cases lr <;> [exists t₂ ^ᵗᵗ t₁; exists t₃ ^ᵗᵗ t₁] <;> grind
    | inr red =>
        obtain ⟨t₁', _⟩ := red
        exists t₁'.case t₂ t₃
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