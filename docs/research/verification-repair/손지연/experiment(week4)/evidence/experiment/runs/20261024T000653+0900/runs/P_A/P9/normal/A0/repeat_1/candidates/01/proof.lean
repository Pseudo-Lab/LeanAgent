by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s1 s2 hr μ
  constructor
  · intro s1' htr
    cases hr with
    | choice h =>
      cases htr with
      | choiceL htr =>
        obtain ⟨q', htr', hq⟩ := h.follow_fst htr
        exact ⟨q', Tr.choiceL htr', ChoiceBisim.bisim hq⟩
      | choiceR htr =>
        exact ⟨s1', Tr.choiceR htr, ChoiceBisim.bisim (by apply HomBisimilarity.refl)⟩
    | bisim h =>
      obtain ⟨q', htr', hq⟩ := h.follow_fst htr
      exact ⟨q', htr', ChoiceBisim.bisim hq⟩
  · intro s2' htr
    cases hr with
    | choice h =>
      cases htr with
      | choiceL htr =>
        obtain ⟨p', htr', hp⟩ := h.follow_snd htr
        exact ⟨p', Tr.choiceL htr', ChoiceBisim.bisim hp⟩
      | choiceR htr =>
        exact ⟨s2', Tr.choiceR htr, ChoiceBisim.bisim (by apply HomBisimilarity.refl)⟩
    | bisim h =>
      obtain ⟨p', htr', hp⟩ := h.follow_snd htr
      exact ⟨p', htr', ChoiceBisim.bisim hp⟩