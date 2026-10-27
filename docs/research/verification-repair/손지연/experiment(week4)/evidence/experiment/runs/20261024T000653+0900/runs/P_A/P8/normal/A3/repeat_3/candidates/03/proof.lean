by
  intro a a₁ a₂ h₁ h₂
  induction h₁ generalizing a₂
  case refl => exact ⟨a₂, h₂, .refl _⟩
  case par a a' b b' ha' hb' iha ihb =>
    cases h₂
    case refl => exact ⟨a' ⬝ b', .refl _, .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      obtain ⟨a₃, ha₁, ha₂⟩ := iha ha''
      obtain ⟨b₃, hb₁, hb₂⟩ := ihb hb''
      exact ⟨a₃ ⬝ b₃, .par ha₁ hb₁, .par ha₂ hb₂⟩
    case red_I =>
      obtain rfl := I_irreducible a' ha'
      exact ⟨b', .red_I _, hb'⟩
    case red_K =>
      obtain ⟨a₂', h, rfl⟩ := Ka_irreducible a₂ a' ha'
      exact ⟨a₂', .red_K _ _, h⟩
    case red_S a c =>
      obtain ⟨a'', c', ha, hc, rfl⟩ := Sab_irreducible a c a' ha'
      exact ⟨a'' ⬝ b' ⬝ (c' ⬝ b'), .red_S ..,
        .par (.par ha hb') (.par hc hb')⟩
  case red_I =>
    cases h₂
    case refl => exact ⟨a₁, .refl _, .red_I _⟩
    case par c a₁' hc ha =>
      obtain rfl := I_irreducible c hc
      exact ⟨a₁', ha, .red_I _⟩
    case red_I => exact ⟨a₁, .refl _, .refl _⟩
  case red_K c =>
    cases h₂
    case refl => exact ⟨a₁, .refl _, .red_K _ _⟩
    case par a' c' ha hc =>
      obtain ⟨a₁', h, rfl⟩ := Ka_irreducible a₁ a' ha
      exact ⟨a₁', h, .red_K _ _⟩
    case red_K => exact ⟨a₁, .refl _, .refl _⟩
  case red_S a b c =>
    cases h₂
    case refl => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .red_S ..⟩
    case par d c' hd hc =>
      obtain ⟨a', b', ha, hb, rfl⟩ := Sab_irreducible a b d hd
      exact ⟨a' ⬝ c' ⬝ (b' ⬝ c'),
        .par (.par ha hc) (.par hb hc), .red_S ..⟩
    case red_S => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .refl _⟩