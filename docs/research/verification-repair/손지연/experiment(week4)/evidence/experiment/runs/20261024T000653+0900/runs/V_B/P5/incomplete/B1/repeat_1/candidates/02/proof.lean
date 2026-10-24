by
  have hMaxwell :=
    (isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ).mp h
  have hGauss : ∀ t x,
      (∇ ⬝ (A.electricField 𝓕.c t)) x =
        𝓕.ε₀⁻¹ * J.chargeDensity 𝓕.c t x := by
    intro t x
    rw [(hMaxwell t x).1]
    simp [div_eq_mul_inv, mul_comm]
  rw [time_deriv_time_deriv_electricField A
    (hA.of_le (ENat.LEInfty.out))]
  simp_rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  simp_rw [hGauss]
  simp only [Time.deriv, Space.deriv]
  simp (disch := fun_prop) [fderiv_fun_sub, fderiv_const_mul, fderiv_fun_sum]
  simp only [FreeSpace.c_sq]
  field_simp
  ring