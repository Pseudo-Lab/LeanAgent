by
  intro a a₁ a₂ h₁ h₂
  cases h₁
  case refl => exact ⟨a₂, h₂, .refl _⟩
  case par a a' b b' ha' hb' =>
    cases h₂
    case refl => exact ⟨a' ⬝ b', .refl _, .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      let ⟨a₃, ha₁, ha₂⟩ := parallelReduction_diamond ha' ha''
      let ⟨b₃, hb₁, hb₂⟩ := parallelReduction_diamond hb' hb''
      exact ⟨a₃ ⬝ b₃, .par ha₁ hb₁, .par ha₂ hb₂⟩
    case red_I =>
      rw [I_irreducible a' ha']
      exact ⟨b', .red_I _, hb'⟩
    case red_K =>
      let ⟨a₂', ha₂', ha'⟩ := Ka_irreducible a₂ a' ha'
      rw [ha']
      exact ⟨a₂', .red_K _ _, ha₂'⟩
    case red_S a c =>
      let ⟨a'', c', ha, hc, ha'⟩ := Sab_irreducible a c a' ha'
      rw [ha']
      exact ⟨a'' ⬝ b' ⬝ (c' ⬝ b'), .red_S _ _ _,
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
    case refl => exact ⟨a₁, .refl _, .red_K _ _⟩
    case par a' c' ha hc =>
      let ⟨a₁', ha₁, ha'⟩ := Ka_irreducible a₁ a' ha
      rw [ha']
      exact ⟨a₁', ha₁, .red_K _ _⟩
    case red_K => exact ⟨a₁, .refl _, .refl _⟩
  case red_S a b c =>
    cases h₂
    case refl => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .red_S _ _ _⟩
    case par d c' hd hc =>
      let ⟨a', b', ha, hb, hd⟩ := Sab_irreducible a b d hd
      rw [hd]
      exact ⟨a' ⬝ c' ⬝ (b' ⬝ c'), .par (.par ha hc) (.par hb hc), .red_S _ _ _⟩
    case red_S => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .refl _⟩