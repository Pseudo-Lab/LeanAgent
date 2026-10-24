by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s₁ s₂ hr μ
  constructor
  · intro s₁' ht
    cases hr with
    | choice h =>
      cases ht with
      | choiceL ht =>
        obtain ⟨s₂', ht', h'⟩ := h.follow_fst ht
        exact ⟨s₂', Tr.choiceL ht', ChoiceBisim.bisim h'⟩
      | choiceR ht =>
        exact ⟨s₁', Tr.choiceR ht, ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
    | bisim h =>
      obtain ⟨s₂', ht', h'⟩ := h.follow_fst ht
      exact ⟨s₂', ht', ChoiceBisim.bisim h'⟩
  · intro s₂' ht
    cases hr with
    | choice h =>
      cases ht with
      | choiceL ht =>
        obtain ⟨s₁', ht', h'⟩ := h.follow_snd ht
        exact ⟨s₁', Tr.choiceL ht', ChoiceBisim.bisim h'⟩
      | choiceR ht =>
        exact ⟨s₂', Tr.choiceR ht, ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
    | bisim h =>
      obtain ⟨s₁', ht', h'⟩ := h.follow_snd ht
      exact ⟨s₁', ht', ChoiceBisim.bisim h'⟩