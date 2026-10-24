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
        obtain ⟨s2', htr', h'⟩ := h.follow_fst htr
        exact ⟨s2', Tr.choiceL htr', ChoiceBisim.bisim h'⟩
      | choiceR htr =>
        refine ⟨s1', Tr.choiceR htr, ChoiceBisim.bisim ?_⟩
        apply HomBisimilarity.refl
    | bisim h =>
      obtain ⟨s2', htr', h'⟩ := h.follow_fst htr
      exact ⟨s2', htr', ChoiceBisim.bisim h'⟩
  · intro s2' htr
    cases hr with
    | choice h =>
      cases htr with
      | choiceL htr =>
        obtain ⟨s1', htr', h'⟩ := h.follow_snd htr
        exact ⟨s1', Tr.choiceL htr', ChoiceBisim.bisim h'⟩
      | choiceR htr =>
        refine ⟨s2', Tr.choiceR htr, ChoiceBisim.bisim ?_⟩
        apply HomBisimilarity.refl
    | bisim h =>
      obtain ⟨s1', htr', h'⟩ := h.follow_snd htr
      exact ⟨s1', htr', ChoiceBisim.bisim h'⟩