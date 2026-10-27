by
  simp only
  intro y
  set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := 1)
    (h_i_add_steps := h_i_succ_lt) (y := y)
  set x₀ := fiberMap 0
  set x₁ := fiberMap 1
  set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) coeffs
  set new_coeffs := fun j : Fin (2 ^ (ℓ - (i + 1))) =>
    (1 - r_chal) * coeffs ⟨j.val * 2, by
      rw [← Nat.add_zero (j.val * 2)]
      exact mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j)
        (b := ℓ - (↑i + 1)) (i := 0) (by omega) (by omega)⟩ +
    r_chal * coeffs ⟨j.val * 2 + 1, by
      exact mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j)
        (b := ℓ - (↑i + 1)) (i := 1) (by omega) (by omega)⟩
  have h_eval_qMap (k : Fin 2) :
      (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval (fiberMap k).val = y.val := by
    have hq := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i
      (by omega) (fiberMap k)
    simp only [Subtype.ext_iff] at hq
    have hy := generates_quotient_point_if_is_fiber_of_y 𝔽q β
      (h_i_add_steps := by omega) (x := fiberMap k) (y := y)
      (hx_is_fiber := by use k)
    exact hq.symm.trans (congrArg (fun z => z.val) hy).symm
  have h_fiber_diff : x₁.val - x₀.val = 1 := by
    have hx₀ := qMap_total_fiber_one_level_eq 𝔽q β i (by omega) y 0
    have hx₁ := qMap_total_fiber_one_level_eq 𝔽q β i (by omega) y 1
    simp only [Fin2ToF2, Fin.isValue, ↓reduceIte, zero_smul, zero_add] at hx₀
    simp only [Fin2ToF2, Fin.isValue, one_ne_zero, ↓reduceIte, one_smul] at hx₁
    change x₀ = _ at hx₀
    change x₁ = _ at hx₁
    rw [hx₁, hx₀]
    simp only [Submodule.coe_add, add_sub_cancel_right, get_sDomain_basis, add_zero]
    rw [normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β]
  set P_i_plus_1 := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i + 1, by omega⟩) new_coeffs
  set P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  set P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  have h_split := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate
    ⟨i, by omega⟩ coeffs
  have h_equation (k : Fin 2) :
      P_i.eval (fiberMap k).val =
        P₀.eval y.val + (fiberMap k).val * P₁.eval y.val := by
    simp only [h_split, Fin.eta, Polynomial.eval_add, eval_comp,
      Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
    rw [h_eval_qMap k]
  have hx₀ : P_i.eval x₀.val = P₀.eval y.val + x₀.val * P₁.eval y.val := by
    simpa only [x₀] using h_equation 0
  have hx₁ : P_i.eval x₁.val = P₀.eval y.val + x₁.val * P₁.eval y.val := by
    simpa only [x₁] using h_equation 1
  have h_poly :
      Polynomial.C (1 - r_chal) * P₀ + Polynomial.C r_chal * P₁ = P_i_plus_1 := by
    simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement, oddRefinement,
      intermediateEvaluationPoly]
    simp_rw [mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Polynomial.C_add, Polynomial.C_mul]
    ring
  set f_i := fun x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ =>
    P_i.eval (x.val : L)
  set f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := h_i_succ_lt)
    (f := f_i) (r_chal := r_chal)
  calc
    f_i_plus_1 y =
        f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
          f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := rfl
    _ = P_i.eval x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
          P_i.eval x₁.val * (r_chal - (1 - r_chal) * x₀.val) := by
      simp only [f_i]
    _ = (P₀.eval y.val + x₀.val * P₁.eval y.val) *
          ((1 - r_chal) * x₁.val - r_chal) +
        (P₀.eval y.val + x₁.val * P₁.eval y.val) *
          (r_chal - (1 - r_chal) * x₀.val) := by rw [hx₀, hx₁]
    _ = P₀.eval y.val * ((1 - r_chal) * (x₁.val - x₀.val)) +
        P₁.eval y.val * ((x₁.val - x₀.val) * r_chal) := by ring
    _ = P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal := by
      rw [h_fiber_diff]
      ring
    _ = (Polynomial.C (1 - r_chal) * P₀ +
          Polynomial.C r_chal * P₁).eval y.val := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      ring
    _ = P_i_plus_1.eval y.val := by rw [h_poly]