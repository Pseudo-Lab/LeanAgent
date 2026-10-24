by
  classical
  simp only
  intro y
  unfold fold
  dsimp only
  have h0 := qMap_total_fiber_one_level_eq 𝔽q β (i := i)
    (h_i_add_1 := by omega) (y := y) (k := (0 : Fin 2))
  have h1 := qMap_total_fiber_one_level_eq 𝔽q β (i := i)
    (h_i_add_1 := by omega) (y := y) (k := (1 : Fin 2))
  simp only at h0 h1
  rw [h0, h1]
  simp [Fin2ToF2, intermediateEvaluationPoly] <;> ring