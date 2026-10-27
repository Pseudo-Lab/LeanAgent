by
  have hmax :=
    (isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ).mp h
  have hamp :
      (fun s => ∂ₜ (A.electricField 𝓕.c · x i) s) =
        fun s =>
          1 / (𝓕.μ₀ * 𝓕.ε₀) *
              ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c s · (j, i)) x -
            (1 / 𝓕.ε₀) * J.currentDensity 𝓕.c s x i := by
    funext s
    simpa (disch := fun_prop) [Time.deriv] using
      time_deriv_electricField_of_isExtrema hA J hJ h s x i
  have hamp' := congrArg (fun f : Time → ℝ => ∂ₜ f t) hamp
  have hgauss :
      (fun y => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) y) =
        fun y => J.chargeDensity 𝓕.c t y / 𝓕.ε₀ := by
    funext y
    simpa [Space.div] using (hmax t y).1
  have hgauss' := congrArg (fun f : Space d → ℝ => ∂[i] f x) hgauss
  simp (disch := fun_prop)
      [Time.deriv, Space.deriv_eq_fderiv_basis,
        fderiv_fun_sub, fderiv_const_mul, fderiv_fun_sum,
        time_deriv_space_deriv_commute,
        time_deriv_magneticFieldMatrix A (hA.of_le (ENat.LEInfty.out)),
        Space.deriv_commute, Finset.sum_sub_distrib] at hamp' hgauss'
  linear_combination (norm := field_simp [FreeSpace.c_sq]) hamp' -
    (𝓕.c ^ 2) * hgauss'