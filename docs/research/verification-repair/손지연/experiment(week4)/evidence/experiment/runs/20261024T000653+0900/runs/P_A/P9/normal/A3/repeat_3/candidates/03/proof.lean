by
  intro h
  use @ChoiceBisim _ _ defs, .choice h
  intro _ _ hs _
  cases hs with
  | choice h =>
    constructor
    · intro s ht
      cases ht with
      | choiceL ht =>
        obtain ⟨q, ht, hb⟩ := h.follow_fst ht
        exact ⟨q, .choiceL ht, .bisim hb⟩
      | choiceR ht => exact ⟨s, .choiceR ht, .bisim (.refl s)⟩
    · intro s ht
      cases ht with
      | choiceL ht =>
        obtain ⟨p, ht, hb⟩ := h.follow_snd ht
        exact ⟨p, .choiceL ht, .bisim hb⟩
      | choiceR ht => exact ⟨s, .choiceR ht, .bisim (.refl s)⟩
  | bisim h =>
    constructor
    · intro _ ht
      obtain ⟨q, ht, hb⟩ := h.follow_fst ht
      exact ⟨q, ht, .bisim hb⟩
    · intro _ ht
      obtain ⟨p, ht, hb⟩ := h.follow_snd ht
      exact ⟨p, ht, .bisim hb⟩