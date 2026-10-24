by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s₁ s₂ hs μ
  cases hs with
  | choice h =>
    constructor
    · intro s' ht
      cases ht with
      | choiceL ht =>
        obtain ⟨q', ht', h'⟩ := h.follow_fst ht
        exact ⟨q', Tr.choiceL ht', ChoiceBisim.bisim h'⟩
      | choiceR ht =>
        exact ⟨s', Tr.choiceR ht, ChoiceBisim.bisim (HomBisimilarity.refl s')⟩
    · intro s' ht
      cases ht with
      | choiceL ht =>
        obtain ⟨p', ht', h'⟩ := h.follow_snd ht
        exact ⟨p', Tr.choiceL ht', ChoiceBisim.bisim h'⟩
      | choiceR ht =>
        exact ⟨s', Tr.choiceR ht, ChoiceBisim.bisim (HomBisimilarity.refl s')⟩
  | bisim h =>
    constructor
    · intro s' ht
      obtain ⟨q', ht', h'⟩ := h.follow_fst ht
      exact ⟨q', ht', ChoiceBisim.bisim h'⟩
    · intro s' ht
      obtain ⟨p', ht', h'⟩ := h.follow_snd ht
      exact ⟨p', ht', ChoiceBisim.bisim h'⟩