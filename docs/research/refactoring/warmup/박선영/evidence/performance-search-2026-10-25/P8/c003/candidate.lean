theorem parallelReduction_diamond : Diamond ParallelReduction := by
  intro a a₁ a₂ h₁
  induction h₁ generalizing a₂ <;> intro h₂
  case refl a => exact ⟨a₂, h₂, .refl a₂⟩
  case par a a' b b' ha' hb' iha ihb =>
    cases h₂
    case refl => exact ⟨_, .refl _, .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      obtain ⟨a₃, ha₁, ha₂⟩ := iha ha''
      obtain ⟨b₃, hb₁, hb₂⟩ := ihb hb''
      exact ⟨_, .par ha₁ hb₁, .par ha₂ hb₂⟩
    case red_I =>
      rw [I_irreducible a' ha']
      exact ⟨b', .red_I b', hb'⟩
    case red_K =>
      obtain ⟨d, hd, rfl⟩ := Ka_irreducible _ a' ha'
      exact ⟨d, .red_K d b', hd⟩
    case red_S a c =>
      obtain ⟨a'', c', ha, hc, rfl⟩ := Sab_irreducible a c a' ha'
      exact ⟨_, .red_S a'' c' b',
        .par (.par ha hb') (.par hc hb')⟩
  case red_I a =>
    cases h₂
    case refl => exact ⟨a, .refl a, .red_I a⟩
    case par c a' hc ha =>
      rw [I_irreducible c hc]
      exact ⟨a', ha, .red_I a'⟩
    case red_I => exact ⟨a, .refl a, .refl a⟩
  case red_K a c =>
    cases h₂
    case refl => exact ⟨a, .refl a, .red_K a c⟩
    case par a' c' ha hc =>
      obtain ⟨d, hd, rfl⟩ := Ka_irreducible a a' ha
      exact ⟨d, hd, .red_K d c'⟩
    case red_K => exact ⟨a, .refl a, .refl a⟩
  case red_S a b c =>
    cases h₂
    case refl => exact ⟨_, .refl _, .red_S a b c⟩
    case par d c' hd hc =>
      obtain ⟨a', b', ha, hb, rfl⟩ := Sab_irreducible a b d hd
      exact ⟨_,
        .par (.par ha hc) (.par hb hc), .red_S a' b' c'⟩
    case red_S => exact ⟨_, .refl _, .refl _⟩
