by
  intro a a₁ a₂ h₁ h₂
  cases h₁
  case refl => exact ⟨a₂, h₂, .refl _⟩
  case par a a' b b' ha' hb' =>
    cases h₂
    case refl => exact ⟨_, .refl _, .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      rcases parallelReduction_diamond ha' ha'' with ⟨a₃, ha₁, ha₂⟩
      rcases parallelReduction_diamond hb' hb'' with ⟨b₃, hb₁, hb₂⟩
      exact ⟨a₃ ⬝ b₃, .par ha₁ hb₁, .par ha₂ hb₂⟩
    case red_I =>
      rw [I_irreducible a' ha']
      exact ⟨b', .red_I _, hb'⟩
    case red_K =>
      rcases Ka_irreducible a₂ a' ha' with ⟨a₂', ha₂', rfl⟩
      exact ⟨a₂', .red_K a₂' b', ha₂'⟩
    case red_S a c =>
      rcases Sab_irreducible a c a' ha' with ⟨a'', c', ha, hc, rfl⟩
      exact ⟨a'' ⬝ b' ⬝ (c' ⬝ b'), .red_S ..,
        .par (.par ha hb') (.par hc hb')⟩
  case red_I =>
    cases h₂
    case refl => exact ⟨a₁, .refl _, .red_I _⟩
    case par c a₁' hc ha =>
      rw [I_irreducible c hc]
      exact ⟨a₁', ha, .red_I _⟩
    case red_I => exact ⟨a₁, .refl _, .refl _⟩
  case red_K c =>
    cases h₂
    case refl => exact ⟨a₁, .refl _, .red_K a₁ c⟩
    case par a' c' ha hc =>
      rcases Ka_irreducible a₁ a' ha with ⟨a₁', ha₁', rfl⟩
      exact ⟨a₁', ha₁', .red_K a₁' c'⟩
    case red_K => exact ⟨a₁, .refl _, .refl _⟩
  case red_S a b c =>
    cases h₂
    case refl => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .red_S ..⟩
    case par d c' hd hc =>
      rcases Sab_irreducible a b d hd with ⟨a', b', ha, hb, rfl⟩
      exact ⟨a' ⬝ c' ⬝ (b' ⬝ c'),
        .par (.par ha hc) (.par hb hc), .red_S ..⟩
    case red_S => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .refl _⟩