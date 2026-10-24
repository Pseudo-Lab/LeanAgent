by
  intro h
  refine ⟨@ChoiceBisim _ _ defs, ChoiceBisim.choice h, ?_⟩
  intro s1 s2 hr μ
  constructor
  · intro s1' htr
    cases hr with
    | choice hbisim =>
      obtain ⟨_, hr, hb⟩ := hbisim
      cases htr with
      | choiceL htr =>
        obtain ⟨s2', htr2, hr2⟩ := hb.follow_fst hr htr
        exact ⟨s2', Tr.choiceL htr2,
          ChoiceBisim.bisim (hb.le_bisimilarity _ _ hr2)⟩
      | choiceR htr =>
        exact ⟨s1', Tr.choiceR htr,
          ChoiceBisim.bisim HomBisimilarity.refl⟩
    | bisim hbisim =>
      obtain ⟨_, hr, hb⟩ := hbisim
      obtain ⟨s2', htr2, hr2⟩ := hb.follow_fst hr htr
      exact ⟨s2', htr2,
        ChoiceBisim.bisim (hb.le_bisimilarity _ _ hr2)⟩
  · intro s2' htr
    cases hr with
    | choice hbisim =>
      obtain ⟨_, hr, hb⟩ := hbisim
      cases htr with
      | choiceL htr =>
        obtain ⟨s1', htr1, hr1⟩ := hb.follow_snd hr htr
        exact ⟨s1', Tr.choiceL htr1,
          ChoiceBisim.bisim (hb.le_bisimilarity _ _ hr1)⟩
      | choiceR htr =>
        exact ⟨s2', Tr.choiceR htr,
          ChoiceBisim.bisim HomBisimilarity.refl⟩
    | bisim hbisim =>
      obtain ⟨_, hr, hb⟩ := hbisim
      obtain ⟨s1', htr1, hr1⟩ := hb.follow_snd hr htr
      exact ⟨s1', htr1,
        ChoiceBisim.bisim (hb.le_bisimilarity _ _ hr1)⟩