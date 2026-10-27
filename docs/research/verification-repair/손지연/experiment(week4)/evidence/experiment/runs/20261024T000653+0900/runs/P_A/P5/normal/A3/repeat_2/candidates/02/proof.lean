by
  let E := A.electricField 𝓕.c
  let B := A.magneticFieldMatrix 𝓕.c
  let K := J.currentDensity 𝓕.c
  let R := J.chargeDensity 𝓕.c
  have hEs : ∀ j, ContDiff ℝ 2 (fun y => E t y j) := fun j =>
    electricField_apply_contDiff_space (i := j) (hA.of_le (right_eq_inf.mp rfl)) t
  have hEd : ∀ j k, Differentiable ℝ (∂[k] (fun y => E t y j)) :=
    fun j k => Space.deriv_differentiable (hEs j) k
  have hBt : ∀ j, Differentiable ℝ (fun s => ∂[j] (fun y => B s y (j, i)) x) := fun j =>
    Space.space_deriv_differentiable_time (i := j)
      (magneticFieldMatrix_contDiff _ (hA.of_le (right_eq_inf.mp rfl)) (j, i)) x
  have hJt : Differentiable ℝ (fun s => K s x i) :=
    LorentzCurrentDensity.currentDensity_apply_differentiable_time
      (hJ.differentiable (by simp)) x i
  have hG := (isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ).mp h
  conv_lhs =>
    enter [1]
    change fun s => ∂ₜ (E · x i) s
    enter [s]
    rw [Time.deriv_euclid (electricField_differentiable_time
      (hA.of_le (right_eq_inf.mp rfl)) _),
      time_deriv_electricField_of_isExtrema hA J hJ h]
  calc
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∂ₜ (fun s => ∑ j, ∂[j] (B s · (j, i)) x) t -
        1 / 𝓕.ε₀ * ∂ₜ (K · x i) t := by
      rw [Time.deriv_eq, fderiv_fun_sub]
      simp only [one_div, mul_inv_rev, FunLike.coe_sub, Pi.sub_apply]
      rw [fderiv_const_mul (Differentiable.fun_sum fun j _ => hBt j).differentiableAt,
        fderiv_const_mul hJt.differentiableAt]
      simp [Time.deriv_eq]
      · exact ((Differentiable.fun_sum fun j _ => hBt j).const_mul _).differentiableAt
      · exact hJt.differentiableAt.const_mul _
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * (∑ j, ∂ₜ (fun s => ∂[j] (B s · (j, i)) x) t) -
        1 / 𝓕.ε₀ * ∂ₜ (K · x i) t := by
      congr
      rw [Time.deriv_eq, fderiv_fun_sum fun j _ => (hBt j).differentiableAt]
      simp only [FunLike.coe_sum, Finset.sum_apply]
      rfl
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * (∑ j, ∂[j] (fun y => ∂ₜ (B · y (j, i)) t) x) -
        1 / 𝓕.ε₀ * ∂ₜ (K · x i) t := by
      congr
      funext j
      rw [Space.time_deriv_comm_space_deriv]
      exact magneticFieldMatrix_contDiff _ (hA.of_le (right_eq_inf.mp rfl)) (j, i)
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * (∑ j, ∂[j]
          (fun y => ∂[j] (E t · i) y - ∂[i] (E t · j) y)) x -
        1 / 𝓕.ε₀ * ∂ₜ (K · x i) t := by
      congr
      simp only [Finset.sum_apply]
      congr
      funext j
      congr
      funext y
      rw [time_deriv_magneticFieldMatrix _ (hA.of_le (ENat.LEInfty.out))]
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j,
          (∂[j] (fun y => ∂[j] (E t · i) y) x -
           ∂[j] (fun y => ∂[i] (E t · j) y) x) -
        1 / 𝓕.ε₀ * ∂ₜ (K · x i) t := by
      congr
      simp only [Finset.sum_apply]
      congr
      funext j
      rw [Space.deriv_eq_fderiv_basis,
        fderiv_fun_sub (hEd _ _).differentiableAt (hEd _ _).differentiableAt]
      simp [← Space.deriv_eq_fderiv_basis]
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, ∂[j] (∂[j] (E t · i)) x -
        1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, ∂[j] (fun y => ∂[i] (E t · j) y) x -
        1 / 𝓕.ε₀ * ∂ₜ (K · x i) t := by simp [mul_sub]
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, ∂[j] (∂[j] (E t · i)) x -
        1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, ∂[i] (fun y => ∂[j] (E t · j) y) x -
        1 / 𝓕.ε₀ * ∂ₜ (K · x i) t := by
      congr
      funext j
      rw [Space.deriv_commute _ (hEs _), Space.deriv_eq_fderiv_basis]
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, ∂[j] (∂[j] (E t · i)) x -
        1 / (𝓕.μ₀ * 𝓕.ε₀) * ∂[i] (fun y => ∑ j, ∂[j] (E t · j) y) x -
        1 / 𝓕.ε₀ * ∂ₜ (K · x i) t := by
      congr
      rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sum]
      simp [← Space.deriv_eq_fderiv_basis]
      intro j _
      exact (hEd j j).differentiableAt
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, ∂[j] (∂[j] (E t · i)) x -
        1 / (𝓕.μ₀ * 𝓕.ε₀) * ∂[i] (fun y => (∇ ⬝ E t) y) x -
        1 / 𝓕.ε₀ * ∂ₜ (K · x i) t := by rfl
    _ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, ∂[j] (∂[j] (E t · i)) x -
        1 / (𝓕.μ₀ * 𝓕.ε₀ ^ 2) * ∂[i] (R t ·) x -
        1 / 𝓕.ε₀ * ∂ₜ (K · x i) t := by
      congr 2
      conv_lhs =>
        enter [2, 2, y]
        rw [(hG t y).1]
      trans 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∂[i] (fun y => (1 / 𝓕.ε₀) * R t y) x
      · congr
        funext y
        ring
      · rw [Space.deriv_eq_fderiv_basis, fderiv_const_mul]
        simp [← Space.deriv_eq_fderiv_basis]
        field_simp
        exact (LorentzCurrentDensity.chargeDensity_differentiable_space
          (hJ.differentiable (by simp)) t).differentiableAt
    _ = 𝓕.c ^ 2 * ∑ j, ∂[j] (∂[j] (E t · i)) x -
        𝓕.c ^ 2 / 𝓕.ε₀ * ∂[i] (R t ·) x -
        𝓕.c ^ 2 * 𝓕.μ₀ * ∂ₜ (K · x i) t := by
      simp [FreeSpace.c_sq]
      field_simp