by
  intro hpq
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice hpq
  intro s₁ s₂ hs μ
  constructor
  · intro s₁' ht
    cases hs with
    | choice hb =>
      cases ht with
      | choiceL ht =>
        obtain ⟨s₂', ht', hb'⟩ := hb.follow_fst ht
        exact ⟨s₂', Tr.choiceL ht', ChoiceBisim.bisim hb'⟩
      | choiceR ht =>
        refine ⟨s₁', Tr.choiceR ht, ChoiceBisim.bisim ?_⟩
        apply HomBisimilarity.refl
    | bisim hb =>
      obtain ⟨s₂', ht', hb'⟩ := hb.follow_fst ht
      exact ⟨s₂', ht', ChoiceBisim.bisim hb'⟩
  · intro s₂' ht
    cases hs with
    | choice hb =>
      cases ht with
      | choiceL ht =>
        obtain ⟨s₁', ht', hb'⟩ := hb.follow_snd ht
        exact ⟨s₁', Tr.choiceL ht', ChoiceBisim.bisim hb'⟩
      | choiceR ht =>
        refine ⟨s₂', Tr.choiceR ht, ChoiceBisim.bisim ?_⟩
        apply HomBisimilarity.refl
    | bisim hb =>
      obtain ⟨s₁', ht', hb'⟩ := hb.follow_snd ht
      exact ⟨s₁', ht', ChoiceBisim.bisim hb'⟩