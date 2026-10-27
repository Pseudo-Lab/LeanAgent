by
  intro h
  use ChoiceBisim, ChoiceBisim.choice h
  intro s₁ s₂ hr μ
  cases hr <;>
    grind [IsBisimulation, ChoiceBisim, HomBisimilarity.refl]