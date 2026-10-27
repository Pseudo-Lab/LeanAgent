by
  simp only
  intro y
  unfold fold
  simp_rw [qMap_total_fiber_one_level_eq 𝔽q β i (by omega)]
  simp [Fin2ToF2, intermediateEvaluationPoly, intermediateNovelBasisX, map_sum] <;>
    ring_nf