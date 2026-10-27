lemma time_deriv_time_deriv_electricField_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema 𝓕 A J)
    (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (∂ₜ (A.electricField 𝓕.c · x i)) t =
      𝓕.c ^ 2 * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
      𝓕.c ^ 2 / 𝓕.ε₀ * ∂[i] (J.chargeDensity 𝓕.c t ·) x -
      𝓕.c ^ 2 * 𝓕.μ₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
  let k := 1 / (𝓕.μ₀ * 𝓕.ε₀)
  have hA₂ : ContDiff ℝ 2 A := hA.of_le (by decide)
  have hA₃ : ContDiff ℝ 3 A := hA.of_le (by decide)
  have hEs := fun j => electricField_apply_contDiff_space (n := 2) (c := 𝓕.c) (i := j) hA₃ t
  have hEd := fun j => Space.deriv_differentiable (hEs j)
  have hBs := magneticFieldMatrix_contDiff (n := 2) (c := 𝓕.c) A hA₃
  have hBt := fun j => Space.space_deriv_differentiable_time (i := j) (hBs (j, i)) x
  have hSum := Differentiable.fun_sum (u := Finset.univ) fun j _ => hBt j
  have hJd := hJ.differentiable (by decide)
  have hJt := LorentzCurrentDensity.currentDensity_apply_differentiable_time (c := 𝓕.c) hJd x i
  calc
    _ = k * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.c t · i) x) x) -
        k * ∑ j, (∂[i] (fun x => ∂[j] (A.electricField 𝓕.c t · j) x) x) -
        1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        conv_lhs =>
          enter [1, t]
          rw [Time.deriv_euclid (electricField_differentiable_time hA₂ _),
            time_deriv_electricField_of_isExtrema hA J hJ h]
        rw [Time.deriv_eq, fderiv_fun_sub (hSum.differentiableAt.const_mul k)
          (hJt.differentiableAt.const_mul _), fderiv_const_mul
          hSum.differentiableAt, fderiv_const_mul hJt.differentiableAt]
        simp only [FunLike.coe_sub, Pi.sub_apply, _root_.smul_apply, smul_eq_mul, ← Time.deriv_eq]
        rw [Time.deriv_fun_sum _ _ fun i _ => (hBt i).differentiableAt]
        simp only [Space.time_deriv_comm_space_deriv (hBs _),
          time_deriv_magneticFieldMatrix _ hA₂, ← mul_sub, ← Finset.sum_sub_distrib]
        congr 3
        funext j
        rw [Space.fun_deriv_sub _ _ (hEd _ _) (hEd _ _)]
        simp only [Pi.sub_apply, sub_right_inj]
        rw [Space.deriv_commute _ (hEs _)]
      _ = _ - 1 / (𝓕.μ₀ * 𝓕.ε₀ ^ 2) * ∂[i] (J.chargeDensity 𝓕.c t ·) x - _ := by
        congr 2
        rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ] at h
        trans k * ∂[i] (fun x => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) x) x
        · rw [Space.deriv_eq_fderiv_basis, fderiv_fun_sum fun j _ => (hEd j j).differentiableAt]
          simp only [_root_.sum_apply, ← deriv_eq_fderiv_basis]
        change _ * ∂[i] (fun x => (∇ ⬝ (A.electricField 𝓕.c t)) x) x = _
        simp only [k, (h t _).1, div_eq_inv_mul, Space.deriv_eq_fderiv_basis, fderiv_const_mul
          ((LorentzCurrentDensity.chargeDensity_differentiable_space hJd t) _)]
        simp only [_root_.smul_apply, smul_eq_mul, ← Space.deriv_eq_fderiv_basis]
        ring1
      _ = _ := by
          rw [FreeSpace.c_sq]
          simp [k, div_eq_mul_inv, pow_two,
            mul_assoc, mul_left_comm, mul_comm]
