by
  intro h
  use @ChoiceBisim _ _ defs, .choice h
  intro _ _ hr _
  constructor
  · intro s' ht
    cases hr with
    | choice h =>
      cases ht with
      | choiceL ht =>
        obtain ⟨q', ht, h'⟩ := h.follow_fst ht
        exact ⟨q', .choiceL ht, .bisim h'⟩
      | choiceR ht =>
        exact ⟨s', .choiceR ht, .bisim (HomBisimilarity.refl _)⟩
    | bisim h =>
      obtain ⟨q', ht, h'⟩ := h.follow_fst ht
      exact ⟨q', ht, .bisim h'⟩
  · intro s' ht
    cases hr with
    | choice h =>
      cases ht with
      | choiceL ht =>
        obtain ⟨p', ht, h'⟩ := h.follow_snd ht
        exact ⟨p', .choiceL ht, .bisim h'⟩
      | choiceR ht =>
        exact ⟨s', .choiceR ht, .bisim (HomBisimilarity.refl _)⟩
    | bisim h =>
      obtain ⟨p', ht, h'⟩ := h.follow_snd ht
      exact ⟨p', ht, .bisim h'⟩