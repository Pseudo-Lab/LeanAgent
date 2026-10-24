by
  dsimp only
  intro y
  simp only [fold]
  simp_rw [qMap_total_fiber_one_level_eq 𝔽q β i (by omega)]
  simp [Fin2ToF2, intermediateEvaluationPoly] <;> ring