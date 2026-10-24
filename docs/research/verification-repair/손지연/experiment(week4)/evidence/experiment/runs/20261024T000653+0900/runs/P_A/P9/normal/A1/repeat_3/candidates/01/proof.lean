by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s1 s2 hr μ
  constructor
  · intro s1' htr
    cases hr
    case choice p q r hbisim =>
      cases htr
      case choiceL a b c htr =>
        obtain ⟨s2', htr2, hbisim'⟩ := hbisim.follow_fst htr
        exact ⟨s2', Tr.choiceL htr2, ChoiceBisim.bisim hbisim'⟩
      case choiceR a b c htr =>
        exact ⟨s1', Tr.choiceR htr,
          ChoiceBisim.bisim (by apply HomBisimilarity.refl)⟩
    case bisim hbisim =>
      obtain ⟨s2', htr2, hbisim'⟩ := hbisim.follow_fst htr
      exact ⟨s2', htr2, ChoiceBisim.bisim hbisim'⟩
  · intro s2' htr
    cases hr
    case choice p q r hbisim =>
      cases htr
      case choiceL a b c htr =>
        obtain ⟨s1', htr1, hbisim'⟩ := hbisim.follow_snd htr
        exact ⟨s1', Tr.choiceL htr1, ChoiceBisim.bisim hbisim'⟩
      case choiceR a b c htr =>
        exact ⟨s2', Tr.choiceR htr,
          ChoiceBisim.bisim (by apply HomBisimilarity.refl)⟩
    case bisim hbisim =>
      obtain ⟨s1', htr1, hbisim'⟩ := hbisim.follow_snd htr
      exact ⟨s1', htr1, ChoiceBisim.bisim hbisim'⟩