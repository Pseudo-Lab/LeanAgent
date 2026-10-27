by
  have hEcd : ∀ k, ContDiff ℝ 2 (fun y => A.electricField 𝓕.c t y k) := by
    intro k
    fun_prop
  have hEsd : ∀ k j, Differentiable ℝ (∂[j] (fun y => A.electricField 𝓕.c t y k)) :=
    fun k j => Space.deriv_differentiable (hEcd k) j
  have hρd : Differentiable ℝ (fun y => J.chargeDensity 𝓕.c t y) := by
    fun_prop
  have hdiv :
      (fun y => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) y) =
        (fun y => J.chargeDensity 𝓕.c t y / 𝓕.ε₀) := by
    funext y
    exact ((isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ).mp h t y).1
  have hcross :
      ∑ j, ∂[j] (∂[i] (A.electricField 𝓕.c t · j)) x =
        𝓕.ε₀⁻¹ * ∂[i] (J.chargeDensity 𝓕.c t ·) x := by
    calc
      ∑ j, ∂[j] (∂[i] (A.electricField 𝓕.c t · j)) x =
          ∂[i] (fun y => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) y) x := by
        conv_lhs =>
          enter [2, j]
          rw [Space.deriv_commute _ (hEcd j)]
        rw [Space.deriv_eq_fderiv_basis]
        rw [fderiv_fun_sum fun j _ => (hEsd j j).differentiableAt]
        simp [← Space.deriv_eq_fderiv_basis]
      _ = ∂[i] (fun y => J.chargeDensity 𝓕.c t y / 𝓕.ε₀) x := by
        rw [hdiv]
      _ = 𝓕.ε₀⁻¹ * ∂[i] (J.chargeDensity 𝓕.c t ·) x := by
        rw [Space.deriv_eq_fderiv_basis]
        have hfun :
            (fun y => J.chargeDensity 𝓕.c t y / 𝓕.ε₀) =
              (fun y => 𝓕.ε₀⁻¹ * J.chargeDensity 𝓕.c t y) := by
          funext y
          simp only [div_eq_mul_inv, mul_comm]
        rw [hfun]
        rw [fderiv_const_mul hρd.differentiableAt]
        simp [← Space.deriv_eq_fderiv_basis]
  have htime_apply (s : Time) :
      ∂ₜ (A.electricField 𝓕.c · x i) s =
        (∂ₜ (A.electricField 𝓕.c · x) s) i := by
    fun_trans <;> fun_prop
  conv_lhs =>
    enter [1, s]
    rw [htime_apply s]
    rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  rw [Time.deriv_sub, Time.deriv_const_mul, Time.deriv_const_mul,
    time_deriv_sum_space_deriv_magneticFieldMatrix
      A (hA.of_le (ENat.LEInfty.out))]
  rw [hcross]
  simp only [Finset.sum_sub_distrib, FreeSpace.c_sq]
  field_simp
  ring
  all_goals fun_prop