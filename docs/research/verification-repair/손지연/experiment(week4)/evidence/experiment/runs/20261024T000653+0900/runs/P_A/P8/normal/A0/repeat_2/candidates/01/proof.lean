by
  intro a a₁ a₂ h₁ h₂
  cases h₁
  case refl => exact ⟨a₂, h₂, .refl a₂⟩
  case par a a' b b' ha' hb' =>
    cases h₂
    case refl => exact ⟨a' ⬝ b', .refl _, .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      obtain ⟨a₃, ha₁, ha₂⟩ := parallelReduction_diamond ha' ha''
      obtain ⟨b₃, hb₁, hb₂⟩ := parallelReduction_diamond hb' hb''
      exact ⟨a₃ ⬝ b₃, .par ha₁ hb₁, .par ha₂ hb₂⟩
    case red_I =>
      rw [I_irreducible a' ha']
      exact ⟨b', .red_I b', hb'⟩
    case red_K =>
      obtain ⟨u, hu, heu⟩ := Ka_irreducible a₂ a' ha'
      rw [heu]
      exact ⟨u, .red_K u b', hu⟩
    case red_S a c =>
      obtain ⟨u, v, hu, hv, heq⟩ := Sab_irreducible a c a' ha'
      rw [heq]
      exact ⟨u ⬝ b' ⬝ (v ⬝ b'), .red_S ..,
        .par (.par hu hb') (.par hv hb')⟩
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
      obtain ⟨u, hu, heu⟩ := Ka_irreducible a₁ a' ha
      rw [heu]
      exact ⟨u, hu, .red_K u c'⟩
    case red_K => exact ⟨a₁, .refl _, .refl _⟩
  case red_S a b c =>
    cases h₂
    case refl => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .red_S ..⟩
    case par d c' hd hc =>
      obtain ⟨u, v, hu, hv, heq⟩ := Sab_irreducible a b d hd
      rw [heq]
      exact ⟨u ⬝ c' ⬝ (v ⬝ c'),
        .par (.par hu hc) (.par hv hc), .red_S ..⟩
    case red_S => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .refl _⟩