by
  intro hpq
  exists @ChoiceBisim _ _ defs
  constructor
  · exact ChoiceBisim.choice hpq
  intro s1 s2 hr μ'
  constructor
  · intro s1' htr
    cases hr
    case choice p q r h =>
      cases htr
      case choiceL htr =>
        obtain ⟨q', htr', hb⟩ := h.follow_fst htr
        exact ⟨q', Tr.choiceL htr', ChoiceBisim.bisim hb⟩
      case choiceR htr =>
        exact ⟨_, Tr.choiceR htr,
          ChoiceBisim.bisim (by grind [HomBisimilarity.refl])⟩
    case bisim p q h =>
      obtain ⟨q', htr', hb⟩ := h.follow_fst htr
      exact ⟨q', htr', ChoiceBisim.bisim hb⟩
  · intro s2' htr
    cases hr
    case choice p q r h =>
      cases htr
      case choiceL htr =>
        obtain ⟨p', htr', hb⟩ := h.follow_snd htr
        exact ⟨p', Tr.choiceL htr', ChoiceBisim.bisim hb⟩
      case choiceR htr =>
        exact ⟨_, Tr.choiceR htr,
          ChoiceBisim.bisim (by grind [HomBisimilarity.refl])⟩
    case bisim p q h =>
      obtain ⟨p', htr', hb⟩ := h.follow_snd htr
      exact ⟨p', htr', ChoiceBisim.bisim hb⟩