by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s1 s2 hr μ
  cases hr <;> grind [IsBisimulation, ChoiceBisim]