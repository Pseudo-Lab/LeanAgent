by
  dsimp only
  intro y
  have hsub : ℓ - (i : ℕ) = (ℓ - ((i : ℕ) + 1)) + 1 := by
    omega
  simp [fold, qMap_total_fiber_one_level_eq, Fin2ToF2,
    intermediateEvaluationPoly, intermediateNovelBasisX, hsub, pow_succ,
    Fin.sum_univ_mul, h_β₀_eq_1.out] <;>
    try omega <;>
    ring