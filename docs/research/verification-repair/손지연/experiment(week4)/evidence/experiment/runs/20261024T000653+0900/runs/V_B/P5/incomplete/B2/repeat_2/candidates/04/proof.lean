by
  have he := (isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ).mp h
  have hcd : ∀ j, ContDiff ℝ 2 (fun y => A.electricField 𝓕.c t y j) := by
    intro j
    simp only [electricField, fieldStrengthMatrix]
    fun_prop
  have hsd : ∀ j k, Differentiable ℝ (∂[k] (fun y => A.electricField 𝓕.c t y j)) :=
    fun j k => Space.deriv_differentiable (hcd j) k
  have hEtd : Differentiable ℝ (fun s => A.electricField 𝓕.c s x) := by
    simp only [electricField, fieldStrengthMatrix]
    fun_prop
  have hEcomp (s : Time) :
      ∂ₜ (fun u => A.electricField 𝓕.c u x i) s =
        (∂ₜ (fun u => A.electricField 𝓕.c u x) s) i := by
    rw [Time.deriv_eq_fderiv_basis, Time.deriv_eq_fderiv_basis]
    fun_trans
  have hBtd : ∀ j, Differentiable ℝ (fun s =>
      ∂[j] (A.magneticFieldMatrix 𝓕.c s · (j, i)) x) := by
    intro j
    simp only [magneticFieldMatrix, fieldStrengthMatrix]
    fun_prop
  have hJtd : Differentiable ℝ (fun s => J.currentDensity 𝓕.c s x i) :=
    LorentzCurrentDensity.currentDensity_apply_differentiable_time
      (hJ.differentiable (by simp)) x i
  have hρd : Differentiable ℝ (fun y => J.chargeDensity 𝓕.c t y) := by
    simp only [LorentzCurrentDensity.chargeDensity]
    fun_prop
  conv_lhs =>
    enter [1, s]
    rw [hEcomp]
    rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  rw [Time.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub
      ((Differentiable.fun_sum fun j _ => hBtd j).const_mul _).differentiableAt
      (hJtd.const_mul _).differentiableAt,
    fderiv_const_mul (Differentiable.fun_sum fun j _ => hBtd j).differentiableAt,
    fderiv_const_mul hJtd.differentiableAt,
    fderiv_fun_sum fun j _ => (hBtd j).differentiableAt]
  simp [← Time.deriv_eq_fderiv_basis]
  simp_rw [time_deriv_space_deriv_magneticFieldMatrix A
    (hA.of_le (ENat.LEInfty.out))]
  have hdsub (j : Fin d) :
      ∂[j] (fun y => ∂[j] (A.electricField 𝓕.c t · i) y -
        ∂[i] (A.electricField 𝓕.c t · j) y) x =
      ∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x -
        ∂[j] (∂[i] (A.electricField 𝓕.c t · j)) x := by
    rw [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub (hsd i j).differentiableAt (hsd j i).differentiableAt]
    simp [← Space.deriv_eq_fderiv_basis]
  simp_rw [hdsub]
  have hcomm (j : Fin d) :
      ∂[j] (∂[i] (A.electricField 𝓕.c t · j)) x =
      ∂[i] (∂[j] (A.electricField 𝓕.c t · j)) x := by
    rw [Space.deriv_commute _ (hcd j)]
  simp_rw [hcomm]
  simp only [Finset.sum_sub_distrib]
  have hsum :
      (∑ j, ∂[i] (∂[j] (A.electricField 𝓕.c t · j)) x) =
      ∂[i] (fun y => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) y) x := by
    rw [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sum fun j _ => (hsd j j).differentiableAt]
    simp [← Space.deriv_eq_fderiv_basis]
  rw [hsum]
  have hdiv :
      (fun y => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) y) =
      (fun y => 𝓕.ε₀⁻¹ * J.chargeDensity 𝓕.c t y) := by
    funext y
    have hy := (he t y).1
    change (∑ j, ∂[j] (A.electricField 𝓕.c t · j) y) = _ at hy
    simpa [div_eq_mul_inv, mul_comm] using hy
  rw [hdiv]
  have hrho :
      ∂[i] (fun y => 𝓕.ε₀⁻¹ * J.chargeDensity 𝓕.c t y) x =
      𝓕.ε₀⁻¹ * ∂[i] (J.chargeDensity 𝓕.c t ·) x := by
    rw [Space.deriv_eq_fderiv_basis]
    rw [fderiv_const_mul hρd.differentiableAt]
    simp [← Space.deriv_eq_fderiv_basis]
  rw [hrho]
  simp only [FreeSpace.c_sq]
  field_simp
  ring