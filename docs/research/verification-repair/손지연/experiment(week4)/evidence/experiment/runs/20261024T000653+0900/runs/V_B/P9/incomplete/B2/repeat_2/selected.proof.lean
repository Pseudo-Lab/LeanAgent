by
  intro h
  exists @ChoiceBisim _ _ defs
  constructor
  · exact ChoiceBisim.choice h
  intro s1 s2 hr μ
  cases hr
  case choice p q r h =>
    constructor
    · intro s' htr
      cases htr
      case choiceL hp =>
        obtain ⟨q', hq, hpq⟩ := h.follow_fst hp
        exact ⟨q', Tr.choiceL hq, ChoiceBisim.bisim hpq⟩
      case choiceR hr =>
        exact ⟨_, Tr.choiceR hr,
          ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
    · intro s' htr
      cases htr
      case choiceL hq =>
        obtain ⟨p', hp, hpq⟩ := h.follow_snd hq
        exact ⟨p', Tr.choiceL hp, ChoiceBisim.bisim hpq⟩
      case choiceR hr =>
        exact ⟨_, Tr.choiceR hr,
          ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
  case bisim h =>
    constructor
    · intro p' hp
      obtain ⟨q', hq, hpq⟩ := h.follow_fst hp
      exact ⟨q', hq, ChoiceBisim.bisim hpq⟩
    · intro q' hq
      obtain ⟨p', hp, hpq⟩ := h.follow_snd hq
      exact ⟨p', hp, ChoiceBisim.bisim hpq⟩