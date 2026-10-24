by
  intro a a₁ a₂ h₁ h₂
  induction h₁ generalizing a₂ with
  | refl a => exact ⟨a₂, h₂, .refl a₂⟩
  | @par a a' b b' ha' hb' iha ihb =>
    cases h₂
    case refl =>
      exact ⟨a' ⬝ b', .refl (a' ⬝ b'), .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      let ⟨a₃, ha⟩ := iha ha''
      let ⟨b₃, hb⟩ := ihb hb''
      exact ⟨a₃ ⬝ b₃, .par ha.1 hb.1, .par ha.2 hb.2⟩
    case red_I =>
      rw [I_irreducible a' ha']
      exact ⟨b', .red_I b', hb'⟩
    case red_K =>
      let ⟨a₂', ha₂'⟩ := Ka_irreducible a₂ a' ha'
      rw [ha₂'.2]
      exact ⟨a₂', .red_K a₂' b', ha₂'.1⟩
    case red_S a c =>
      let ⟨a'', c', h⟩ := Sab_irreducible a c a' ha'
      rw [h.2.2]
      exact ⟨a'' ⬝ b' ⬝ (c' ⬝ b'), .red_S a'' c' b',
        .par (.par h.1 hb') (.par h.2.1 hb')⟩
  | red_I a =>
    cases h₂
    case refl => exact ⟨a, .refl a, .red_I a⟩
    case par c a' hc ha =>
      rw [I_irreducible c hc]
      exact ⟨a', ha, .red_I a'⟩
    case red_I => exact ⟨a, .refl a, .refl a⟩
  | red_K a b =>
    cases h₂
    case refl => exact ⟨a, .refl a, .red_K a b⟩
    case par a' b' ha hb =>
      let ⟨a'', h⟩ := Ka_irreducible a a' ha
      rw [h.2]
      exact ⟨a'', h.1, .red_K a'' b'⟩
    case red_K => exact ⟨a, .refl a, .refl a⟩
  | red_S a b c =>
    cases h₂
    case refl =>
      exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .red_S ..⟩
    case par d c' hd hc =>
      let ⟨a', b', h⟩ := Sab_irreducible a b d hd
      rw [h.2.2]
      exact ⟨a' ⬝ c' ⬝ (b' ⬝ c'),
        .par (.par h.1 hc) (.par h.2.1 hc), .red_S ..⟩
    case red_S =>
      exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .refl _⟩