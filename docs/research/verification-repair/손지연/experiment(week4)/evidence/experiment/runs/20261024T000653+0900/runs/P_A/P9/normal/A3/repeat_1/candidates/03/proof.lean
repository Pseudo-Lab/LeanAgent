by
  intro h
  use @ChoiceBisim _ _ defs, .choice h
  intro _ _ hr _
  cases hr with
  | choice h =>
    constructor <;> intro s' ht
    · cases ht with
      | choiceL ht =>
        obtain ⟨q', ht, h'⟩ := h.follow_fst ht
        exact ⟨q', .choiceL ht, .bisim h'⟩
      | choiceR ht => exact ⟨s', .choiceR ht, .bisim (.refl _)⟩
    · cases ht with
      | choiceL ht =>
        obtain ⟨p', ht, h'⟩ := h.follow_snd ht
        exact ⟨p', .choiceL ht, .bisim h'⟩
      | choiceR ht => exact ⟨s', .choiceR ht, .bisim (.refl _)⟩
  | bisim h =>
    constructor <;> intro s' ht
    · obtain ⟨q', ht, h'⟩ := h.follow_fst ht
      exact ⟨q', ht, .bisim h'⟩
    · obtain ⟨p', ht, h'⟩ := h.follow_snd ht
      exact ⟨p', ht, .bisim h'⟩