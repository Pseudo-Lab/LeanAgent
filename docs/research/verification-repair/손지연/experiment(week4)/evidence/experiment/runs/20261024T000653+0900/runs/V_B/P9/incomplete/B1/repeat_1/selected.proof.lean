by
  intro h
  exists @ChoiceBisim _ _ defs
  constructor
  · exact ChoiceBisim.choice h
  intro s1 s2 hr μ
  constructor
  case left =>
    intro s1' htr
    cases hr
    case choice p q r h =>
      unfold lts at *
      cases htr
      case choiceL htr =>
        obtain ⟨q', htr', hbisim⟩ := h.follow_fst htr
        exists q'
        constructor
        · exact Tr.choiceL htr'
        · exact ChoiceBisim.bisim hbisim
      case choiceR htr =>
        exists s1'
        constructor
        · exact Tr.choiceR htr
        · exact ChoiceBisim.bisim (by grind [HomBisimilarity.refl])
    case bisim h =>
      obtain ⟨q', htr', hbisim⟩ := h.follow_fst htr
      exact ⟨q', htr', ChoiceBisim.bisim hbisim⟩
  case right =>
    intro s2' htr
    cases hr
    case choice p q r h =>
      unfold lts at *
      cases htr
      case choiceL htr =>
        obtain ⟨p', htr', hbisim⟩ := h.follow_snd htr
        exists p'
        constructor
        · exact Tr.choiceL htr'
        · exact ChoiceBisim.bisim hbisim
      case choiceR htr =>
        exists s2'
        constructor
        · exact Tr.choiceR htr
        · exact ChoiceBisim.bisim (by grind [HomBisimilarity.refl])
    case bisim h =>
      obtain ⟨p', htr', hbisim⟩ := h.follow_snd htr
      exact ⟨p', htr', ChoiceBisim.bisim hbisim⟩