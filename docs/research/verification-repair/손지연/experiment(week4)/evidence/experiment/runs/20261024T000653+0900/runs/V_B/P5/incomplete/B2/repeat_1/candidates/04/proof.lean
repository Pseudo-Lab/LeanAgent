by
  have hcd : ∀ j, ContDiff ℝ 2 (fun y => A.electricField 𝓕.c t y j) :=
    fun j => electricField_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)) t j
  have hBd : ∀ j, Differentiable ℝ
      (fun s => ∂[j] (A.magneticFieldMatrix 𝓕.c s · (j, i)) x) := by
    intro j
    rw [Space.deriv_eq_fderiv_basis]
    unfold magneticFieldMatrix
    fun_prop
  have hρd : Differentiable ℝ (fun y => J.chargeDensity 𝓕.c t y) := by
    unfold LorentzCurrentDensity.chargeDensity
    fun_prop
  have hJtd : Differentiable ℝ (fun s => J.currentDensity 𝓕.c s x i) := by
    unfold LorentzCurrentDensity.currentDensity
    fun_prop
  have hEt : Differentiable ℝ (fun s => A.electricField 𝓕.c s x) := by
    unfold electricField
    fun_prop
  have hsd : ∀ j, Differentiable ℝ (∂[j] (fun y => A.electricField 𝓕.c t y j)) :=
    fun j => Space.deriv_differentiable (hcd j) j
  have hgauss :
      (fun y => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) y) =
        (fun y => 𝓕.ε₀⁻¹ * J.chargeDensity 𝓕.c t y) := by
    funext y
    have hy := ((isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ).mp h t y).1
    simpa [Space.div, div_eq_mul_inv, mul_comm] using hy
  have hdiv :
      ∑ j, ∂[j] (∂[i] (A.electricField 𝓕.c t · j)) x =
        𝓕.ε₀⁻¹ * ∂[i] (J.chargeDensity 𝓕.c t ·) x := by
    calc
      ∑ j, ∂[j] (∂[i] (A.electricField 𝓕.c t · j)) x =
          ∑ j, ∂[i] (∂[j] (A.electricField 𝓕.c t · j)) x := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Space.deriv_commute _ (hcd j)]
      _ = ∂[i] (fun y => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) y) x := by
            rw [Space.deriv_eq_fderiv_basis]
            rw [fderiv_fun_sum fun j _ => (hsd j).differentiableAt]
            simp [← Space.deriv_eq_fderiv_basis]
      _ = ∂[i] (fun y => 𝓕.ε₀⁻¹ * J.chargeDensity 𝓕.c t y) x := by
            rw [hgauss]
      _ = 𝓕.ε₀⁻¹ * ∂[i] (J.chargeDensity 𝓕.c t ·) x := by
            rw [Space.deriv_eq_fderiv_basis,
              fderiv_const_mul hρd.differentiableAt]
            simp [← Space.deriv_eq_fderiv_basis]
  rw [show ∂ₜ (A.electricField 𝓕.c · x i) =
      (fun s => 1 / (𝓕.μ₀ * 𝓕.ε₀) *
        ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c s · (j, i)) x -
        (1 / 𝓕.ε₀) * J.currentDensity 𝓕.c s x i) by
      funext s
      calc
        ∂ₜ (A.electricField 𝓕.c · x i) s =
            ∂ₜ (A.electricField 𝓕.c · x) s i := by
              change (fderiv ℝ (fun s => A.electricField 𝓕.c s x i) s) 1 =
                (fderiv ℝ (fun s => A.electricField 𝓕.c s x) s) 1 i
              simpa using congrArg (fun q : ℝ →L[ℝ] ℝ => q 1)
                (hEt.differentiableAt.hasFDerivAt.apply i).fderiv
        _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) *
            ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c s · (j, i)) x -
            (1 / 𝓕.ε₀) * J.currentDensity 𝓕.c s x i :=
              time_deriv_electricField_of_isExtrema hA J hJ h s x i]
  change (fderiv ℝ
      (fun s => 1 / (𝓕.μ₀ * 𝓕.ε₀) *
        ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c s · (j, i)) x -
        (1 / 𝓕.ε₀) * J.currentDensity 𝓕.c s x i) t) 1 = _
  rw [fderiv_fun_sub
      ((Differentiable.fun_sum fun j _ => hBd j).const_mul _).differentiableAt
      (hJtd.const_mul _).differentiableAt,
    fderiv_const_mul
      (Differentiable.fun_sum fun j _ => hBd j).differentiableAt,
    fderiv_const_mul hJtd.differentiableAt,
    fderiv_fun_sum fun j _ => (hBd j).differentiableAt]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    Finset.sum_apply, smul_eq_mul]
  simp_rw [time_deriv_space_deriv_magneticFieldMatrix A
    (hA.of_le (ENat.LEInfty.out))]
  simp only [Finset.sum_sub_distrib]
  rw [hdiv]
  simp [FreeSpace.c_sq]
  field_simp
  ring