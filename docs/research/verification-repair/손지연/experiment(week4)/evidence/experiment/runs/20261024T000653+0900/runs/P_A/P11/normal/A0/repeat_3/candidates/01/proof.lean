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
        (b := ℓ - (↑i + 1)) (i := 0) (by omega) (by omega)⟩ +
    r_chal * coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j)
        (b := ℓ - (↑i + 1)) (i := 1) (by omega) (by omega)⟩
  have h_eval_qMap (k : Fin 2) :
      (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval (fiberMap k).val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i
      (by omega) (fiberMap k)
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    have h_res := (is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1)
      (by omega) (x := fiberMap k) (y := y)).mpr (by
        rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
  have h_eval_qMap_x₀ := h_eval_qMap (0 : Fin 2)
  have h_eval_qMap_x₁ := h_eval_qMap (1 : Fin 2)
  have h_fiber_diff : x₁.val - x₀.val = 1 := by
    have hx₀' := qMap_total_fiber_one_level_eq 𝔽q β i (by omega) y (0 : Fin 2)
    have hx₁' := qMap_total_fiber_one_level_eq 𝔽q β i (by omega) y (1 : Fin 2)
    simp only [Fin2ToF2, Fin.isValue, ↓reduceIte, zero_smul, zero_add] at hx₀'
    simp only [Fin2ToF2, Fin.isValue, ↓reduceIte, one_smul] at hx₁'
    dsimp only [x₁, x₀, fiberMap]
    rw [hx₁', hx₀']
    simp only [AddSubmonoidClass.coe_add, add_sub_cancel_right, get_sDomain_basis,
      Fin.coe_ofNat_eq_mod, zero_mod, add_zero, cast_eq]
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
  set f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) =>
    P_i.eval (x.val : L)
  set f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := by omega)
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
    _ = P₀.eval y.val *
          ((1 - r_chal) * x₁.val - r_chal + r_chal -
            (1 - r_chal) * x₀.val) +
        P₁.eval y.val *
          (x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
            x₁.val * (r_chal - (1 - r_chal) * x₀.val)) := by ring
    _ = P₀.eval y.val * ((1 - r_chal) * (x₁.val - x₀.val)) +
        P₁.eval y.val * ((x₁.val - x₀.val) * r_chal) := by ring
    _ = P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal := by
      rw [h_fiber_diff]
      ring
    _ = P_i_plus_1.eval y.val := by
      simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement, oddRefinement,
        intermediateEvaluationPoly]
      conv_lhs => enter [1]; rw [mul_comm, ← Polynomial.eval_C_mul]
      conv_lhs => enter [2]; rw [mul_comm, ← Polynomial.eval_C_mul]
      rw [← Polynomial.eval_add]
      congr
      simp_rw [mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Polynomial.C_add, Polynomial.C_mul]
      ring