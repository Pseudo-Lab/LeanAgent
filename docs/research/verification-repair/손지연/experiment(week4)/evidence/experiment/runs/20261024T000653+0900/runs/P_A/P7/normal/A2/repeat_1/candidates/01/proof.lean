by
  generalize eq : [] = Γ at der
  have der' : Typing Γ t τ := der
  induction der <;> subst eq
  case var mem => grind
  case app t₁ _ _ t₂ l r ih_l ih_r =>
    right
    cases ih_l rfl l with
    | inl val_l =>
        cases ih_r rfl r with
        | inl val_r =>
            obtain ⟨_, u, h⟩ := l.canonical_form_abs val_l
            exact ⟨u ^ᵗᵗ t₂, by grind⟩
        | inr red_r =>
            obtain ⟨u, hu⟩ := red_r
            exact ⟨t₁.app u, by grind⟩
    | inr red_l =>
        obtain ⟨u, hu⟩ := red_l
        exact ⟨u.app t₂, by grind⟩
  case tapp σ' der _ ih =>
    right
    cases ih rfl der with
    | inl val =>
        obtain ⟨_, u, h⟩ := der.canonical_form_tabs val
        exact ⟨u ^ᵗᵞ σ', by grind⟩
    | inr red =>
        obtain ⟨u, hu⟩ := red
        exact ⟨.tapp u σ', by grind⟩
  case let' t₁ σ t₂ τ L der _ ih _ =>
    right
    cases ih rfl der with
    | inl val => exact ⟨t₂ ^ᵗᵗ t₁, by grind⟩
    | inr red =>
        obtain ⟨u, hu⟩ := red
        exact ⟨u.let' t₂, by grind⟩
  case inl der _ ih =>
    cases ih rfl der with
    | inl val => grind
    | inr red =>
        right
        obtain ⟨u, hu⟩ := red
        exact ⟨.inl u, by grind⟩
  case inr der _ ih =>
    cases ih rfl der with
    | inl val => grind
    | inr red =>
        right
        obtain ⟨u, hu⟩ := red
        exact ⟨.inr u, by grind⟩
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    right
    cases ih rfl der with
    | inl val =>
        have ⟨u, lr⟩ := der.canonical_form_sum val
        cases lr <;> [exact ⟨t₂ ^ᵗᵗ u, by grind⟩; exact ⟨t₃ ^ᵗᵗ u, by grind⟩]
    | inr red =>
        obtain ⟨u, hu⟩ := red
        exact ⟨u.case t₂ t₃, by grind⟩
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