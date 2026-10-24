by
  dsimp only
  intro y
  simp [fold, qMap_total_fiber_one_level_eq, Fin2ToF2,
    intermediateEvaluationPoly, h_β₀_eq_1.out] <;>
    try omega <;>
    ring