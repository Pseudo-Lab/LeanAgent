by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s₁ s₂ hr μ
  constructor
  case left =>
    intro s₁' ht
    cases hr
    case choice p q r h =>
      cases ht
      case choiceL a b c ht =>
        obtain ⟨q', ht, h'⟩ := h.follow_fst ht
        exact ⟨q', Tr.choiceL ht, ChoiceBisim.bisim h'⟩
      case choiceR a b c ht =>
        exact ⟨s₁', Tr.choiceR ht, ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
    case bisim h =>
      obtain ⟨q', ht, h'⟩ := h.follow_fst ht
      exact ⟨q', ht, ChoiceBisim.bisim h'⟩
  case right =>
    intro s₂' ht
    cases hr
    case choice p q r h =>
      cases ht
      case choiceL a b c ht =>
        obtain ⟨p', ht, h'⟩ := h.follow_snd ht
        exact ⟨p', Tr.choiceL ht, ChoiceBisim.bisim h'⟩
      case choiceR a b c ht =>
        exact ⟨s₂', Tr.choiceR ht, ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
    case bisim h =>
      obtain ⟨p', ht, h'⟩ := h.follow_snd ht
      exact ⟨p', ht, ChoiceBisim.bisim h'⟩