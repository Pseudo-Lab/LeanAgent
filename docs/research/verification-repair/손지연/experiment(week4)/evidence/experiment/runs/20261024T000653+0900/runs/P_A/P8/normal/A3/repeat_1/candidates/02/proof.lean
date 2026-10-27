by
  intro a a₁ a₂ h₁ h₂
  cases h₁
  case refl => exact ⟨_, h₂, .refl _⟩
  case par a a' b b' ha' hb' =>
    cases h₂
    case refl => exact ⟨_, .refl _, .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      let ⟨a₃, ha⟩ := parallelReduction_diamond ha' ha''
      let ⟨b₃, hb⟩ := parallelReduction_diamond hb' hb''
      exact ⟨_, .par ha.1 hb.1, .par ha.2 hb.2⟩
    case red_I =>
      rw [I_irreducible a' ha']
      exact ⟨_, .red_I b', hb'⟩
    case red_K =>
      let ⟨a₂', h⟩ := Ka_irreducible a₂ a' ha'
      rw [h.2]
      exact ⟨_, .red_K a₂' b', h.1⟩
    case red_S a c =>
      let ⟨a'', c', h⟩ := Sab_irreducible a c a' ha'
      rw [h.2.2]
      exact ⟨_, .red_S .., .par (.par h.1 hb') (.par h.2.1 hb')⟩
  case red_I =>
    cases h₂
    case refl => exact ⟨_, .refl _, .red_I _⟩
    case par c a₁' hc ha =>
      rw [I_irreducible c hc]
      exact ⟨_, ha, .red_I _⟩
    case red_I => exact ⟨_, .refl _, .refl _⟩
  case red_K c =>
    cases h₂
    case refl => exact ⟨_, .refl _, .red_K _ c⟩
    case par a' c' ha hc =>
      let ⟨a₁', h⟩ := Ka_irreducible a₁ a' ha
      rw [h.2]
      exact ⟨_, h.1, .red_K a₁' c'⟩
    case red_K => exact ⟨_, .refl _, .refl _⟩
  case red_S a b c =>
    cases h₂
    case refl => exact ⟨_, .refl _, .red_S ..⟩
    case par d c' hd hc =>
      let ⟨a', b', h⟩ := Sab_irreducible a b d hd
      rw [h.2.2]
      exact ⟨_, .par (.par h.1 hc) (.par h.2.1 hc), .red_S ..⟩
    case red_S => exact ⟨_, .refl _, .refl _⟩