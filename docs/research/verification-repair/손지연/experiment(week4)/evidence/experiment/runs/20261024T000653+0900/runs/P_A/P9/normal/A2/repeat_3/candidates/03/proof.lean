by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s₁ s₂ hs μ
  constructor
  · intro s₁' ht
    cases hs with
    | choice h =>
      cases ht with
      | choiceL ht =>
        obtain ⟨s₂', ht, hb⟩ := h.follow_fst ht
        exact ⟨s₂', Tr.choiceL ht, ChoiceBisim.bisim hb⟩
      | choiceR ht =>
        exact ⟨s₁', Tr.choiceR ht, ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
    | bisim h =>
      obtain ⟨s₂', ht, hb⟩ := h.follow_fst ht
      exact ⟨s₂', ht, ChoiceBisim.bisim hb⟩
  · intro s₂' ht
    cases hs with
    | choice h =>
      cases ht with
      | choiceL ht =>
        obtain ⟨s₁', ht, hb⟩ := h.follow_snd ht
        exact ⟨s₁', Tr.choiceL ht, ChoiceBisim.bisim hb⟩
      | choiceR ht =>
        exact ⟨s₂', Tr.choiceR ht, ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
    | bisim h =>
      obtain ⟨s₁', ht, hb⟩ := h.follow_snd ht
      exact ⟨s₁', ht, ChoiceBisim.bisim hb⟩