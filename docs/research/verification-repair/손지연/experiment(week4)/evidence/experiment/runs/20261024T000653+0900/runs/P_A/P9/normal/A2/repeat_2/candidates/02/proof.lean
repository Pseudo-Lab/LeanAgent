by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s₁ s₂ hs μ
  cases hs <;>
    grind [IsBisimulation, ChoiceBisim, HomBisimilarity.refl]