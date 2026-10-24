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
      obtain ⟨a₂', ha₂', rfl⟩ := Ka_irreducible a₂ a' ha'
      exact ⟨a₂', .red_K a₂' b', ha₂'⟩
    case red_S a c =>
      obtain ⟨a'', c', ha, hc, rfl⟩ := Sab_irreducible a c a' ha'
      exact ⟨a'' ⬝ b' ⬝ (c' ⬝ b'), .red_S a'' c' b',
        .par (.par ha hb') (.par hc hb')⟩
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
      obtain ⟨a₁', ha₁', rfl⟩ := Ka_irreducible a₁ a' ha
      exact ⟨a₁', ha₁', .red_K a₁' c'⟩
    case red_K => exact ⟨a₁, .refl a₁, .refl a₁⟩
  case red_S a b c =>
    cases h₂
    case refl => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .red_S ..⟩
    case par d c' hd hc =>
      obtain ⟨a', b', ha, hb, rfl⟩ := Sab_irreducible a b d hd
      exact ⟨a' ⬝ c' ⬝ (b' ⬝ c'),
        .par (.par ha hc) (.par hb hc), .red_S ..⟩
    case red_S => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .refl _⟩