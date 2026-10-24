by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s₁ s₂ hs μ
  constructor
  · intro s₁' ht
    cases hs with
    | choice hb =>
      cases ht with
      | choiceL ht =>
        obtain ⟨q', ht', hb'⟩ := hb.follow_fst ht
        exact ⟨q', Tr.choiceL ht', ChoiceBisim.bisim hb'⟩
      | choiceR ht =>
        refine ⟨s₁', Tr.choiceR ht, ChoiceBisim.bisim ?_⟩
        apply HomBisimilarity.refl
    | bisim hb =>
      obtain ⟨q', ht', hb'⟩ := hb.follow_fst ht
      exact ⟨q', ht', ChoiceBisim.bisim hb'⟩
  · intro s₂' ht
    cases hs with
    | choice hb =>
      cases ht with
      | choiceL ht =>
        obtain ⟨p', ht', hb'⟩ := hb.follow_snd ht
        exact ⟨p', Tr.choiceL ht', ChoiceBisim.bisim hb'⟩
      | choiceR ht =>
        refine ⟨s₂', Tr.choiceR ht, ChoiceBisim.bisim ?_⟩
        apply HomBisimilarity.refl
    | bisim hb =>
      obtain ⟨p', ht', hb'⟩ := hb.follow_snd ht
      exact ⟨p', ht', ChoiceBisim.bisim hb'⟩