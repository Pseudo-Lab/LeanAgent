by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s₁ s₂ hs μ
  cases hs with
  | choice h =>
    obtain ⟨R, hpq, hR⟩ := h
    constructor <;> intro s' ht <;> cases ht <;>
      grind [IsBisimulation, IsBisimulation.le_bisimilarity,
        HomBisimilarity.refl, ChoiceBisim]
  | bisim h =>
    grind [IsBisimulation, IsBisimulation.le_bisimilarity, ChoiceBisim]