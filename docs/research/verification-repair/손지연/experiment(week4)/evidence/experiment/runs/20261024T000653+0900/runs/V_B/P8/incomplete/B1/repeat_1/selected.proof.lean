by
  intro x y z hxy hxz
  induction hxy generalizing z
  case refl =>
    exact ⟨z, hxz, ParallelReduction.refl z⟩
  case red_I a =>
    cases hxz
    case refl =>
      exact ⟨a, ParallelReduction.refl a, ParallelReduction.red_I a⟩
    case red_I =>
      exact ⟨a, ParallelReduction.refl a, ParallelReduction.refl a⟩
    case par u v hu hv =>
      rw [I_irreducible _ hu]
      exact ⟨v, hv, ParallelReduction.red_I v⟩
  case red_K a b =>
    cases hxz
    case refl =>
      exact ⟨a, ParallelReduction.refl a, ParallelReduction.red_K a b⟩
    case red_K =>
      exact ⟨a, ParallelReduction.refl a, ParallelReduction.refl a⟩
    case par u v hu hv =>
      obtain ⟨d, hd, hdu⟩ := Ka_irreducible a u hu
      rw [hdu]
      exact ⟨d, hd, ParallelReduction.red_K d v⟩
  case red_S a b c =>
    cases hxz
    case refl =>
      exact ⟨a ⬝ c ⬝ (b ⬝ c), ParallelReduction.refl _,
        ParallelReduction.red_S a b c⟩
    case red_S =>
      exact ⟨a ⬝ c ⬝ (b ⬝ c), ParallelReduction.refl _, ParallelReduction.refl _⟩
    case par u v hu hv =>
      obtain ⟨d, e, hd, he, hdu⟩ := Sab_irreducible a b u hu
      rw [hdu]
      refine ⟨_, ?_, ParallelReduction.red_S d e v⟩
      exact ParallelReduction.par
        (ParallelReduction.par hd hv)
        (ParallelReduction.par he hv)
  case par a a' b b' ha hb iha ihb =>
    cases hxz
    case refl =>
      exact ⟨a' ⬝ b', ParallelReduction.refl _, ParallelReduction.par ha hb⟩
    case red_I =>
      rw [I_irreducible _ ha]
      exact ⟨b', ParallelReduction.red_I b', hb⟩
    case red_K =>
      obtain ⟨d, hd, hda⟩ := Ka_irreducible z a' ha
      rw [hda]
      exact ⟨d, ParallelReduction.red_K d b', hd⟩
    case red_S c d =>
      obtain ⟨e, f, he, hf, hea⟩ := Sab_irreducible c d a' ha
      rw [hea]
      refine ⟨_, ParallelReduction.red_S e f b', ?_⟩
      exact ParallelReduction.par
        (ParallelReduction.par he hb)
        (ParallelReduction.par hf hb)
    case par c c' hc hd =>
      obtain ⟨e, hae, hce⟩ := iha hc
      obtain ⟨f, hbf, hdf⟩ := ihb hd
      exact ⟨e ⬝ f, ParallelReduction.par hae hbf, ParallelReduction.par hce hdf⟩