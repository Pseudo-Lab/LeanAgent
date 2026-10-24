by
  intro a a₁ a₂ h₁ h₂
  cases h₁
  case refl => exact ⟨_, h₂, .refl _⟩
  case par a a' b b' ha' hb' =>
    cases h₂
    case refl => exact ⟨_, .refl _, .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      obtain ⟨a₃, ha₁, ha₂⟩ := parallelReduction_diamond ha' ha''
      obtain ⟨b₃, hb₁, hb₂⟩ := parallelReduction_diamond hb' hb''
      exact ⟨_, .par ha₁ hb₁, .par ha₂ hb₂⟩
    case red_I =>
      obtain rfl := I_irreducible a' ha'
      exact ⟨_, .red_I _, hb'⟩
    case red_K =>
      obtain ⟨a₂', ha₂', rfl⟩ := Ka_irreducible a₂ a' ha'
      exact ⟨_, .red_K _ _, ha₂'⟩
    case red_S a c =>
      obtain ⟨a'', c', ha'', hc', rfl⟩ := Sab_irreducible a c a' ha'
      exact ⟨_, .red_S _ _ _, .par (.par ha'' hb') (.par hc' hb')⟩
  case red_I =>
    cases h₂
    case refl => exact ⟨_, .refl _, .red_I _⟩
    case par c a₁' hc ha =>
      obtain rfl := I_irreducible c hc
      exact ⟨_, ha, .red_I _⟩
    case red_I => exact ⟨_, .refl _, .refl _⟩
  case red_K c =>
    cases h₂
    case refl => exact ⟨_, .refl _, .red_K _ c⟩
    case par a' c' ha hc =>
      obtain ⟨a₁', ha₁', rfl⟩ := Ka_irreducible a₁ a' ha
      exact ⟨_, ha₁', .red_K _ c'⟩
    case red_K => exact ⟨_, .refl _, .refl _⟩
  case red_S a b c =>
    cases h₂
    case refl => exact ⟨_, .refl _, .red_S ..⟩
    case par d c' hd hc =>
      obtain ⟨a', b', ha', hb', rfl⟩ := Sab_irreducible a b d hd
      exact ⟨_, .par (.par ha' hc) (.par hb' hc), .red_S ..⟩
    case red_S => exact ⟨_, .refl _, .refl _⟩