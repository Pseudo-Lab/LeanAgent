by
  intro a b c hab hac
  induction hab generalizing c
  case refl a =>
    exact ⟨c, hac, ParallelReduction.refl c⟩
  case red_I a =>
    cases hac
    case refl =>
      exact ⟨a, ParallelReduction.refl a, ParallelReduction.red_I a⟩
    case red_I =>
      exact ⟨a, ParallelReduction.refl a, ParallelReduction.refl a⟩
    case par b a' hI ha =>
      obtain rfl := I_irreducible b hI
      exact ⟨a', ha, ParallelReduction.red_I a'⟩
  case red_K a b =>
    cases hac
    case refl =>
      exact ⟨a, ParallelReduction.refl a, ParallelReduction.red_K a b⟩
    case red_K =>
      exact ⟨a, ParallelReduction.refl a, ParallelReduction.refl a⟩
    case par c b' hc hb =>
      obtain ⟨a', ha, rfl⟩ := Ka_irreducible a c hc
      exact ⟨a', ha, ParallelReduction.red_K a' b'⟩
  case red_S a b c =>
    cases hac
    case refl =>
      exact
        ⟨a ⬝ c ⬝ (b ⬝ c), ParallelReduction.refl _,
          ParallelReduction.red_S a b c⟩
    case red_S =>
      exact ⟨a ⬝ c ⬝ (b ⬝ c), ParallelReduction.refl _, ParallelReduction.refl _⟩
    case par d c' hd hc =>
      obtain ⟨a', b', ha, hb, rfl⟩ := Sab_irreducible a b d hd
      exact
        ⟨a' ⬝ c' ⬝ (b' ⬝ c'),
          ParallelReduction.par (ParallelReduction.par ha hc)
            (ParallelReduction.par hb hc),
          ParallelReduction.red_S a' b' c'⟩
  case par a a' b b' ha hb iha ihb =>
    cases hac
    case refl =>
      exact
        ⟨a' ⬝ b', ParallelReduction.refl _, ParallelReduction.par ha hb⟩
    case red_I =>
      obtain rfl := I_irreducible a' ha
      exact ⟨b', ParallelReduction.red_I b', hb⟩
    case red_K =>
      obtain ⟨c', hc, rfl⟩ := Ka_irreducible c a' ha
      exact ⟨c', ParallelReduction.red_K c' b', hc⟩
    case red_S x y =>
      obtain ⟨x', y', hx, hy, rfl⟩ := Sab_irreducible x y a' ha
      exact
        ⟨x' ⬝ b' ⬝ (y' ⬝ b'), ParallelReduction.red_S x' y' b',
          ParallelReduction.par (ParallelReduction.par hx hb)
            (ParallelReduction.par hy hb)⟩
    case par a₂ b₂ ha₂ hb₂ =>
      obtain ⟨a₃, ha₁, ha₂'⟩ := iha ha₂
      obtain ⟨b₃, hb₁, hb₂'⟩ := ihb hb₂
      exact
        ⟨a₃ ⬝ b₃, ParallelReduction.par ha₁ hb₁,
          ParallelReduction.par ha₂' hb₂'⟩