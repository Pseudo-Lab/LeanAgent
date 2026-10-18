theorem bisimilarity_congr_choice :
    (p ~[lts (defs := defs)] q) → (choice p r) ~[lts (defs := defs)] (choice q r) := by
  intro h
  exists @ChoiceBisim _ _ defs
  constructor
  · constructor; assumption
  intro s1 s2 r μ
  constructor
  case left =>
    intro s1' htr
    cases r
    case choice p q r hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      cases htr
      case choiceL a b c htr =>
        obtain ⟨s2', htr2, hr2⟩ := hb.follow_fst hr htr
        exact ⟨s2', Tr.choiceL htr2, .bisim (hb.le_bisimilarity _ _ hr2)⟩
      case choiceR a b c htr =>
        exists s1'
        constructor
        · apply Tr.choiceR htr
        · constructor
          apply HomBisimilarity.refl
    case bisim hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      obtain ⟨s2', htr2, hr2⟩ := hb.follow_fst hr htr
      exists s2'
      constructor
      · assumption
      constructor
      apply hb.le_bisimilarity _ _ hr2
  case right =>
    intro s2' htr
    cases r
    case choice p q r hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      cases htr
      case choiceL a b c htr =>
        obtain ⟨s1', htr1, hr1⟩ := hb.follow_snd hr htr
        exact ⟨s1', Tr.choiceL htr1, .bisim (hb.le_bisimilarity _ _ hr1)⟩
      case choiceR a b c htr =>
        exists s2'
        constructor
        · apply Tr.choiceR htr
        · constructor
          apply HomBisimilarity.refl
    case bisim hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      obtain ⟨s1', htr1, hr1⟩ := hb.follow_snd hr htr
      exists s1'
      constructor
      · assumption
      · constructor
        apply hb.le_bisimilarity _ _ hr1
