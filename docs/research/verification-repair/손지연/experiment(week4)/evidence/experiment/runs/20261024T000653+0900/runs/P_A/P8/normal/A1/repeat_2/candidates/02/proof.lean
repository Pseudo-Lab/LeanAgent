by
  intro a a₁ a₂ h₁ h₂
  cases h₁
  case refl => exact ⟨a₂, h₂, .refl _⟩
  case par a a' b b' ha hb =>
    cases h₂
    case refl => exact ⟨a' ⬝ b', .refl _, .par ha hb⟩
    case par a'' b'' ha' hb' =>
      rcases parallelReduction_diamond ha ha' with ⟨a₃, ha₁, ha₂⟩
      rcases parallelReduction_diamond hb hb' with ⟨b₃, hb₁, hb₂⟩
      exact ⟨a₃ ⬝ b₃, .par ha₁ hb₁, .par ha₂ hb₂⟩
    case red_I =>
      rw [I_irreducible a' ha]
      exact ⟨b', .red_I _, hb⟩
    case red_K =>
      rcases Ka_irreducible a₂ a' ha with ⟨x, hx, hax⟩
      rw [hax]
      exact ⟨x, .red_K x b', hx⟩
    case red_S a c =>
      rcases Sab_irreducible a c a' ha with ⟨x, y, hx, hy, hxy⟩
      rw [hxy]
      exact ⟨x ⬝ b' ⬝ (y ⬝ b'), .red_S ..,
        .par (.par hx hb) (.par hy hb)⟩
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
      rcases Ka_irreducible a₁ a' ha with ⟨x, hx, hax⟩
      rw [hax]
      exact ⟨x, hx, .red_K x c'⟩
    case red_K => exact ⟨a₁, .refl _, .refl _⟩
  case red_S a b c =>
    cases h₂
    case refl => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .red_S ..⟩
    case par d c' hd hc =>
      rcases Sab_irreducible a b d hd with ⟨x, y, hx, hy, hxy⟩
      rw [hxy]
      exact ⟨x ⬝ c' ⬝ (y ⬝ c'),
        .par (.par hx hc) (.par hy hc), .red_S ..⟩
    case red_S => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .refl _⟩