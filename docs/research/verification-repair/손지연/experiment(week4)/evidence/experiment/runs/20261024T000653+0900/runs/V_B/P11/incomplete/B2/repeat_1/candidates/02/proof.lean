by
  classical
  simp only
  intro y
  have h₀ := qMap_total_fiber_one_level_eq 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (by omega) y (0 : Fin 2)
  have h₁ := qMap_total_fiber_one_level_eq 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (by omega) y (1 : Fin 2)
  simp only at h₀ h₁
  simp only [fold]
  rw [h₀, h₁]
  have hsub : ℓ - i.val = (ℓ - (i.val + 1)) + 1 := by
    omega
  simp [Fin2ToF2, intermediateEvaluationPoly, intermediateNovelBasisX,
    hsub, pow_succ, Fin.sum_univ_mul, h_β₀_eq_1.out,
    Submodule.coe_add, Submodule.coe_smul] <;> ring