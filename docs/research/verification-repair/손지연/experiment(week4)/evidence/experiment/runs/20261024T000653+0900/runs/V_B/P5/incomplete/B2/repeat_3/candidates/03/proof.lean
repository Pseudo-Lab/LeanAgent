by
  have hMax := (isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ).mp h
  have hGauss :
      (fun y => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) y) =
        fun y => J.chargeDensity 𝓕.c t y / 𝓕.ε₀ := by
    funext y
    exact (hMax t y).1
  conv_lhs =>
    enter [1, s]
    rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  simp (disch := fun_prop)
  simp_rw [time_deriv_magneticFieldMatrix A (hA.of_le (right_eq_inf.mp rfl))]
  simp (disch := fun_prop)
  simp only [Finset.sum_sub_distrib]
  conv_lhs =>
    enter [1, 2, j, 2]
    rw [Space.deriv_commute _
      (electricField_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)) t j)]
  rw [← Space.deriv_fun_sum]
  rw [hGauss]
  simp (disch := fun_prop)
  simp only [FreeSpace.c_sq]
  field_simp
  ring