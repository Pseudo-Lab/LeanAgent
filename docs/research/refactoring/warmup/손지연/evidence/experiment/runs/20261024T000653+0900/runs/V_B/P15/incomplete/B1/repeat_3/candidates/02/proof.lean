by
  intro d e f h i
  rcases (hrelation d e).mp h.1 with ⟨_, hde⟩
  rcases (hrelation e f).mp h.2 with ⟨_, hef⟩
  have hde0 := hde (0 : Fin 9)
  have hde1 := hde (1 : Fin 9)
  have hde2 := hde (2 : Fin 9)
  have hde3 := hde (3 : Fin 9)
  have hde4 := hde (4 : Fin 9)
  have hde5 := hde (5 : Fin 9)
  have hde6 := hde (6 : Fin 9)
  have hde7 := hde (7 : Fin 9)
  have hde8 := hde (8 : Fin 9)
  have hef0 := hef (0 : Fin 9)
  have hef1 := hef (1 : Fin 9)
  have hef2 := hef (2 : Fin 9)
  have hef3 := hef (3 : Fin 9)
  have hef4 := hef (4 : Fin 9)
  have hef5 := hef (5 : Fin 9)
  have hef6 := hef (6 : Fin 9)
  have hef7 := hef (7 : Fin 9)
  have hef8 := hef (8 : Fin 9)
  norm_num [hdigits_to_num, Fin.sum_univ_succ] at hde0 hde1 hde2 hde3 hde4 hde5 hde6 hde7 hde8 hef0 hef1 hef2 hef3 hef4 hef5 hef6 hef7 hef8
  fin_cases i <;> norm_num at ⊢ <;> omega