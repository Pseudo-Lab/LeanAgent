by
  intro h
  use @ChoiceBisim _ _ defs, ChoiceBisim.choice h
  intro s1 s2 hr μ
  cases hr
  case choice h =>
    constructor <;> intro s htr <;> cases htr <;>
      grind [IsBisimulation, ChoiceBisim, HomBisimilarity.refl]
  case bisim h =>
    grind [IsBisimulation, ChoiceBisim]