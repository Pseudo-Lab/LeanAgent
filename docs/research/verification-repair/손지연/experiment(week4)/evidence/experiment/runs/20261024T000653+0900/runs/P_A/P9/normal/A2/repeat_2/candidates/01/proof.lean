by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s₁ s₂ hs μ
  cases hs with
  | bisim h =>
    constructor
    · intro s₁' ht
      obtain ⟨s₂', ht', h'⟩ := h.follow_fst ht
      exact ⟨s₂', ht', ChoiceBisim.bisim h'⟩
    · intro s₂' ht
      obtain ⟨s₁', ht', h'⟩ := h.follow_snd ht
      exact ⟨s₁', ht', ChoiceBisim.bisim h'⟩
  | choice h =>
    constructor
    · intro s₁' ht
      cases ht with
      | choiceL ht =>
        obtain ⟨s₂', ht', h'⟩ := h.follow_fst ht
        exact ⟨s₂', Tr.choiceL ht', ChoiceBisim.bisim h'⟩
      | choiceR ht =>
        refine ⟨s₁', Tr.choiceR ht, ChoiceBisim.bisim ?_⟩
        apply HomBisimilarity.refl
    · intro s₂' ht
      cases ht with
      | choiceL ht =>
        obtain ⟨s₁', ht', h'⟩ := h.follow_snd ht
        exact ⟨s₁', Tr.choiceL ht', ChoiceBisim.bisim h'⟩
      | choiceR ht =>
        refine ⟨s₂', Tr.choiceR ht, ChoiceBisim.bisim ?_⟩
        apply HomBisimilarity.refl