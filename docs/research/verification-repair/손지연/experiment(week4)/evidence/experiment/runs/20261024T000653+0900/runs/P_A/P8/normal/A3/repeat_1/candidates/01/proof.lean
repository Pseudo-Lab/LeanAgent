by
  intro a a₁ a₂ h₁ h₂
  cases h₁
  case refl => exact ⟨a₂, h₂, .refl a₂⟩
  case par a a' b b' ha' hb' =>
    cases h₂
    case refl => exact ⟨a' ⬝ b', .refl _, .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      let ⟨a₃, ha⟩ := parallelReduction_diamond ha' ha''
      let ⟨b₃, hb⟩ := parallelReduction_diamond hb' hb''
      exact ⟨a₃ ⬝ b₃, .par ha.1 hb.1, .par ha.2 hb.2⟩
    case red_I =>
      rw [I_irreducible a' ha']
      exact ⟨b', .red_I b', hb'⟩
    case red_K =>
      let ⟨a₂', h⟩ := Ka_irreducible a₂ a' ha'
      rw [h.2]
      exact ⟨a₂', .red_K a₂' b', h.1⟩
    case red_S a c =>
      let ⟨a'', c', h⟩ := Sab_irreducible a c a' ha'
      rw [h.2.2]
      exact ⟨a'' ⬝ b' ⬝ (c' ⬝ b'), .red_S ..,
        .par (.par h.1 hb') (.par h.2.1 hb')⟩
  case red_I =>
    cases h₂
    case refl => exact ⟨a₁, .refl a₁, .red_I a₁⟩
    case par c a₁' hc ha =>
      rw [I_irreducible c hc]
      exact ⟨a₁', ha, .red_I a₁'⟩
    case red_I => exact ⟨a₁, .refl a₁, .refl a₁⟩
  case red_K c =>
    cases h₂
    case refl => exact ⟨a₁, .refl a₁, .red_K a₁ c⟩
    case par a' c' ha hc =>
      let ⟨a₁', h⟩ := Ka_irreducible a₁ a' ha
      rw [h.2]
      exact ⟨a₁', h.1, .red_K a₁' c'⟩
    case red_K => exact ⟨a₁, .refl a₁, .refl a₁⟩
  case red_S a b c =>
    cases h₂
    case refl => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .red_S ..⟩
    case par d c' hd hc =>
      let ⟨a', b', h⟩ := Sab_irreducible a b d hd
      rw [h.2.2]
      exact ⟨a' ⬝ c' ⬝ (b' ⬝ c'),
        .par (.par h.1 hc) (.par h.2.1 hc), .red_S ..⟩
    case red_S => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .refl _⟩