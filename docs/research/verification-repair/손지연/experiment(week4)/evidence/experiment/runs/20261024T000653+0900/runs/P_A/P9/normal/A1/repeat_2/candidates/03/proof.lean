by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s1 s2 hr μ
  constructor
  · intro s1' ht
    cases hr with
    | choice hbisim =>
      obtain ⟨rel, hrel, hb⟩ := hbisim
      cases ht with
      | choiceL ht =>
        obtain ⟨s2', ht', hrel'⟩ := hb.follow_fst hrel ht
        exact ⟨s2', Tr.choiceL ht',
          ChoiceBisim.bisim (hb.le_bisimilarity _ _ hrel')⟩
      | choiceR ht =>
        exact ⟨s1', Tr.choiceR ht,
          ChoiceBisim.bisim HomBisimilarity.refl⟩
    | bisim hbisim =>
      obtain ⟨rel, hrel, hb⟩ := hbisim
      obtain ⟨s2', ht', hrel'⟩ := hb.follow_fst hrel ht
      exact ⟨s2', ht', ChoiceBisim.bisim
        (hb.le_bisimilarity _ _ hrel')⟩
  · intro s2' ht
    cases hr with
    | choice hbisim =>
      obtain ⟨rel, hrel, hb⟩ := hbisim
      cases ht with
      | choiceL ht =>
        obtain ⟨s1', ht', hrel'⟩ := hb.follow_snd hrel ht
        exact ⟨s1', Tr.choiceL ht',
          ChoiceBisim.bisim (hb.le_bisimilarity _ _ hrel')⟩
      | choiceR ht =>
        exact ⟨s2', Tr.choiceR ht,
          ChoiceBisim.bisim HomBisimilarity.refl⟩
    | bisim hbisim =>
      obtain ⟨rel, hrel, hb⟩ := hbisim
      obtain ⟨s1', ht', hrel'⟩ := hb.follow_snd hrel ht
      exact ⟨s1', ht', ChoiceBisim.bisim
        (hb.le_bisimilarity _ _ hrel')⟩