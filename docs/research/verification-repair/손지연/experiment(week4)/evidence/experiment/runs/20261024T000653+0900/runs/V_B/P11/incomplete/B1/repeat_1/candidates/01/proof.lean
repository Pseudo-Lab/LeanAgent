by
  dsimp only
  intro y
  have h₀ := qMap_total_fiber_one_level_eq
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 𝔽q β i (by omega) y (0 : Fin 2)
  have h₁ := qMap_total_fiber_one_level_eq
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 𝔽q β i (by omega) y (1 : Fin 2)
  dsimp only at h₀ h₁
  simp [Fin2ToF2] at h₀ h₁
  simp [fold, h₀, h₁, intermediateEvaluationPoly]
  <;> ring