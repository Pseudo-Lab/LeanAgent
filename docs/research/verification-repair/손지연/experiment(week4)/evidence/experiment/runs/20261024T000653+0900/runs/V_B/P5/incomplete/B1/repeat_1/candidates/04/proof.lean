by
  have hMaxwell :=
    (isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ).mp h
  have hGauss : ∀ t x,
      (∇ ⬝ (A.electricField 𝓕.c t)) x =
        𝓕.ε₀⁻¹ * J.chargeDensity 𝓕.c t x := by
    intro t x
    rw [(hMaxwell t x).1]
    simp [div_eq_mul_inv, mul_comm]
  have hTimeDerivApply (s : Time) :
      ∂ₜ (A.electricField 𝓕.c · x i) s =
        (∂ₜ (A.electricField 𝓕.c · x) s) i := by
    simp only [Time.deriv]
    simp (disch := fun_prop)
  conv_lhs =>
    enter [2, s]
    rw [hTimeDerivApply]
    rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  simp only [Time.deriv, Space.deriv]
  simp (disch := fun_prop)
    [fderiv_fun_sub, fderiv_const_mul, fderiv_fun_sum,
      time_deriv_space_deriv_commute, time_deriv_magneticFieldMatrix]
  simp_rw [hGauss]
  simp (disch := fun_prop)
    [fderiv_fun_sub, fderiv_const_mul, fderiv_fun_sum,
      Space.deriv_commute]
  simp only [FreeSpace.c_sq]
  field_simp
  ring