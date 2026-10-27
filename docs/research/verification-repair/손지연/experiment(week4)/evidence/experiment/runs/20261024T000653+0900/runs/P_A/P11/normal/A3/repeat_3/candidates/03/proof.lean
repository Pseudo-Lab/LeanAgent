by
  simp only
  intro y
  set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := 1)
    (h_i_add_steps := by simp only; omega) (y := y)
  set x₀ := fiberMap 0
  set x₁ := fiberMap 1
  set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) coeffs
  set new_coeffs := fun j : Fin (2 ^ (ℓ - (i + 1))) =>
    (1 - r_chal) * coeffs ⟨j.val * 2, by
      rw [← Nat.add_zero (j.val * 2)]
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j)
        (b := ℓ - (↑i + 1)) (i := 0) <;> omega
    ⟩ + r_chal * coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j)
        (b := ℓ - (↑i + 1)) (i := 1) <;> omega
    ⟩
  have h_eval_qMap_x₀ : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₀.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i (by omega) x₀
    simp only [Subtype.ext_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) (by omega)
      (x := x₀) (y := y).mpr (by
        rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
  have h_eval_qMap_x₁ : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₁.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i (by omega) x₁
    simp only [Subtype.ext_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) (by omega)
      (x := x₁) (y := y).mpr (by
        rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by
    simp only
    omega)
  let y_lifted : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ :=
    sDomain.lift 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
      (j := ⟨i.val + 1, by omega⟩) (h_j := by exact h_i_succ_lt)
      (h_le := by apply Fin.mk_le_mk.mpr; omega) y
  have h0 : 0 < ℓ + 𝓡 - i.val := by omega
  let j₀ : Fin (ℓ + 𝓡 - i.val) := ⟨0, h0⟩
  have hx₀ : x₀ = y_lifted := by
    simpa [x₀, fiberMap, basis_x, y_lifted, Fin2ToF2] using
      (qMap_total_fiber_one_level_eq 𝔽q β i (by omega) y (0 : Fin 2))
  have hx₁ : x₁ = basis_x j₀ + y_lifted := by
    simpa [x₁, fiberMap, basis_x, y_lifted, j₀, Fin2ToF2] using
      (qMap_total_fiber_one_level_eq 𝔽q β i (by omega) y (1 : Fin 2))
  have h_fiber_diff : x₁.val - x₀.val = 1 := by
    rw [hx₁, hx₀]
    simp only [Submodule.coe_add, add_sub_cancel_right, j₀, basis_x, get_sDomain_basis]
    rw [normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β]
  set P_i_plus_1 := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i + 1, by omega⟩) new_coeffs
  set P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  set P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  have h_P_i_eval := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate
    ⟨i, by omega⟩ coeffs
  have h_equation_39_x₀ :
      P_i.eval x₀.val = P₀.eval y.val + x₀.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Fin.eta, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₀, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  have h_equation_39_x₁ :
      P_i.eval x₁.val = P₀.eval y.val + x₁.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Fin.eta, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₁, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  set f_i := fun x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ =>
    P_i.eval (x.val : L)
  set f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := h_i_succ_lt)
    (f := f_i) (r_chal := r_chal)
  have h_fold_def : f_i_plus_1 y =
      f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
      f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := rfl
  calc
    f_i_plus_1 y =
        f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
        f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := h_fold_def
    _ = P_i.eval x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
        P_i.eval x₁.val * (r_chal - (1 - r_chal) * x₀.val) := by
      simp only [f_i]
    _ = (P₀.eval y.val + x₀.val * P₁.eval y.val) *
          ((1 - r_chal) * x₁.val - r_chal) +
        (P₀.eval y.val + x₁.val * P₁.eval y.val) *
          (r_chal - (1 - r_chal) * x₀.val) := by
      rw [h_equation_39_x₀, h_equation_39_x₁]
    _ = P₀.eval y.val * ((1 - r_chal) * x₁.val - r_chal + r_chal -
          (1 - r_chal) * x₀.val) +
        P₁.eval y.val * (x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
          x₁.val * (r_chal - (1 - r_chal) * x₀.val)) := by ring
    _ = P₀.eval y.val * ((1 - r_chal) * (x₁.val - x₀.val)) +
        P₁.eval y.val * ((x₁.val - x₀.val) * r_chal) := by ring
    _ = P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal := by
      rw [h_fiber_diff]
      ring
    _ = P_i_plus_1.eval y.val := by
      have hp : Polynomial.C (1 - r_chal) * P₀ + Polynomial.C r_chal * P₁ =
          P_i_plus_1 := by
        simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement, oddRefinement,
          intermediateEvaluationPoly]
        simp_rw [mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Polynomial.C_add, Polynomial.C_mul]
        ring
      rw [← hp]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      ring