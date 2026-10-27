theorem parallelReduction_diamond : Diamond ParallelReduction := by
  intro a a₁ a₂ h₁ h₂
  induction h₁ generalizing a₂
  case refl => use a₂, h₂, .refl a₂
  all_goals cases h₂
  case' par.par iha ihb _ _ ha'' hb'' =>
    rcases iha ha'', ihb hb'' with ⟨⟨_, ha⟩, ⟨_, hb⟩⟩
    exact ⟨_, ha.1.par hb.1, ha.2.par hb.2⟩
  case' par.red_I b' _ _ ha' _ =>
    cases I_irreducible _ ha'
    use b', .red_I b'
  case' par.red_K ha' _ | red_K.par ha' _ =>
    obtain ⟨k, h, rfl⟩ := Ka_irreducible _ _ ha'
    refine ⟨k, ?_, ?_⟩ <;> first | assumption | constructor
  case' par.red_S hb' _ _ _ ha' _ | red_S.par ha' hb' =>
    obtain ⟨_, _, ha, hc, rfl⟩ := Sab_irreducible _ _ _ ha'
    have hj := (ha.par hb').par (hc.par hb')
    first
    | exact ⟨_, hj, .red_S ..⟩
    | exact ⟨_, .red_S .., hj⟩
  case' red_I.par a₁' hc ha =>
    cases I_irreducible _ hc
    use a₁', ha, .red_I _
  all_goals exact ⟨_, .refl _, by constructor <;> assumption⟩
