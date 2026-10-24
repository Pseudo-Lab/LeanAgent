theorem fold_advances_evaluation_poly
  (i : Fin (ℓ)) (h_i_succ_lt : i + 1 < ℓ + 𝓡)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L) (r_chal : L) :
  let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by
    exact Nat.lt_trans (n := i) (k := ℓ+1) (m := ℓ) (h₁ := i.isLt) (by exact Nat.lt_add_one ℓ)
  ⟩) coeffs
  let f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_trans (n := i) (k := r) (m := ℓ) (h₁ := by omega) (by omega)⟩) =>
    P_i.eval (x.val : L)
  let f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := by omega) (f := f_i) (r_chal := r_chal)
  let new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      rw [←Nat.add_zero (j.val * 2)]
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
        (i := 0) (by omega) (by omega)
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
        (i := 1) (by omega) (by omega)
    ⟩)
  let P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i+1, by omega⟩) new_coeffs
  ∀ (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i+1, by omega⟩), f_i_plus_1 y = P_i_plus_1.eval y.val := by
  simp only
  intro y
  set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := 1)
    (h_i_add_steps := by simp only; omega) (y := y)
  set x₀ := fiberMap 0
  set x₁ := fiberMap 1
  set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) coeffs
  set new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      have h : j.val * 2 < 2^(ℓ - (i + 1)) * 2 := by omega
      have h2 : 2^(ℓ - i) = 2^(ℓ - (i + 1)) * 2 := by
        conv_rhs => enter[2]; rw [←Nat.pow_one 2]
        rw [←pow_add]; congr
        rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega)]
        -- ⊢ ℓ - ↑i = ℓ - (↑i + 1 - 1)
        rw [Nat.add_sub_cancel (n := i) (m := 1)]
      omega
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1)) (i := 1)
      · omega
      · omega
    ⟩)
  have h_eval_qMap_x₀ : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₀.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i (by omega) x₀
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) (by omega)
      (x := x₀) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
    -- exact qMap_eval_fiber_eq_self ⟦L⟧ ⟨i + 1, by omega⟩ (by simp only; omega) h_i_succ_lt y 0
  have h_eval_qMap_x₁ : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₁.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i (by omega) x₁
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) (by omega)
      (x := x₁) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
  have hx₀ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)
    (h_i_add_steps := by omega) y 0
  have hx₁ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)
    (h_i_add_steps := by omega) y 1
  simp only [Fin.isValue] at hx₀ hx₁

  have h_fiber_diff : x₁.val - x₀.val = 1 := by
    simp only [Fin.isValue, x₁, x₀, fiberMap]
    rw [hx₁, hx₀]
    simp only [Fin.isValue, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    have h_index : ℓ + 𝓡 - i = (ℓ + 𝓡 - (i.val + 1)) + 1 := by omega
    rw! (castMode := .all) [h_index]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] -- (free_term + y_repr) - (free_term + y_repr) = 1
    -- First, simplify the free terms
    simp only [fiber_coeff, eqRec_eq_cast, lt_one_iff, reducePow, Fin.isValue,
      Fin.coe_ofNat_eq_mod, mod_succ, dite_smul, ite_smul, zero_smul, one_smul, zero_mod]
    have h_cast_0 :
        (cast (Eq.symm h_index ▸ rfl : Fin (ℓ + 𝓡 - (↑i + 1) + 1) = Fin (ℓ + 𝓡 - ↑i)) 0).val =
        0 := by
      rw [←Fin.cast_eq_cast (h := by omega)]
      rw [Fin.cast_val_eq_val (h_eq := by omega)]
      simp only [Fin.coe_ofNat_eq_mod, mod_succ_eq_iff_lt, succ_eq_add_one, lt_add_iff_pos_left]
      omega
    have h_cast_1 :
        (cast (Eq.symm h_index ▸ rfl : Fin (ℓ + 𝓡 - (↑i + 1) + 1) = Fin (ℓ + 𝓡 - ↑i)) 1).val =
        1 := by
      rw [←Fin.cast_eq_cast (h := by omega)]
      rw [Fin.cast_val_eq_val (h_eq := by omega)]
      simp only [Fin.coe_ofNat_eq_mod, mod_succ_eq_iff_lt, succ_eq_add_one,
        lt_add_iff_pos_left, tsub_pos_iff_lt]
      omega
    simp only [h_cast_0, ↓reduceDIte]
    have h_getBit_0_of_0 : Nat.getBit (k := 0) (n := 0) = 0 := by
      simp only [getBit, shiftRight_zero, and_one_is_mod, zero_mod]
    have h_getBit_0_of_1 : Nat.getBit (k := 0) (n := 1) = 1 := by
      simp only [getBit, shiftRight_zero, Nat.and_self]
    simp only [h_getBit_0_of_1, one_ne_zero, ↓reduceIte, h_getBit_0_of_0, zero_add]
    rw! (castMode := .all) [←h_index]
    rw [cast_eq]
    simp only [get_sDomain_basis, Fin.coe_ofNat_eq_mod, zero_mod, add_zero, cast_eq]
    rw [normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β]
    ring_nf
    conv_rhs => rw [←add_zero (a := 1)]
    rw [add_sub_assoc]
    congr 1
    rw [sub_eq_zero]
    apply Finset.sum_congr (h := by rfl)
    simp only [mem_univ, congr_eqRec, Fin.val_succ, Nat.add_eq_zero, one_ne_zero, and_false,
      ↓reduceDIte, add_tsub_cancel_right, Fin.eta, imp_self, implies_true]
  set P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i+1, by omega⟩) new_coeffs
  -- Set up the even and odd refinement polynomials
  set P₀_coeffs := fun j : Fin (2^(ℓ - (i + 1))) => coeffs ⟨j.val * 2, by
    have h1 : ℓ - (i + 1) + 1 = ℓ - i := by omega
    have h2 : 2^(ℓ - (i + 1) + 1) = 2^(ℓ - i) := by rw [h1]
    have h3 : 2^(ℓ - (i + 1)) * 2 = 2^(ℓ - (i + 1) + 1) := by rw [pow_succ]
    rw [← h2, ← h3]; omega⟩
  set P₁_coeffs := fun j : Fin (2^(ℓ - (i + 1))) => coeffs ⟨j.val * 2 + 1, by
    have h1 : ℓ - (i + 1) + 1 = ℓ - i := by omega
    have h2 : 2^(ℓ - (i + 1) + 1) = 2^(ℓ - i) := by rw [h1]
    have h3 : 2^(ℓ - (i + 1)) * 2 = 2^(ℓ - (i + 1) + 1) := by rw [pow_succ]
    rw [← h2, ← h3]; omega⟩
  set P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  set P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  have h_P_i_eval := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ coeffs
  -- Equation 39 : P^(i)(X) = P₀^(i+1)(q^(i)(X)) + X · P₁^(i+1)(q^(i)(X))
  have h_equation_39_x₀ : P_i.eval x₀.val = P₀.eval y.val + x₀.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Fin.eta, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₀, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  have h_equation_39_x₁ : P_i.eval x₁.val = P₀.eval y.val + x₁.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Fin.eta, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₁, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  set f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) => P_i.eval (x.val : L)
  set f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := by omega) (f := f_i) (r_chal := r_chal)
  -- Unfold the definition of f_i_plus_1 using the fold function
  have h_fold_def : f_i_plus_1 y =
      f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
      f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := rfl
  -- Main calculation following the outline
  calc f_i_plus_1 y
    = f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
        f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := h_fold_def
    _ = P_i.eval x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
        P_i.eval x₁.val * (r_chal - (1 - r_chal) * x₀.val) := by simp only [f_i]
    _ = (P₀.eval y.val + x₀.val * P₁.eval y.val) * ((1 - r_chal) * x₁.val - r_chal) +
        (P₀.eval y.val + x₁.val * P₁.eval y.val) * (r_chal - (1 - r_chal) * x₀.val) := by
      rw [h_equation_39_x₀, h_equation_39_x₁]
    _ = P₀.eval y.val * ((1 - r_chal) * x₁.val - r_chal + r_chal - (1 - r_chal) * x₀.val) +
        P₁.eval y.val * (x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
          x₁.val * (r_chal - (1 - r_chal) * x₀.val)) := by ring
    _ = P₀.eval y.val * ((1 - r_chal) * (x₁.val - x₀.val)) +
        P₁.eval y.val * ((x₁.val - x₀.val) * r_chal) := by ring
    _ = P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal := by rw [h_fiber_diff]; ring
    _ = P_i_plus_1.eval y.val := by
      simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement, oddRefinement,
        intermediateEvaluationPoly]
      conv_lhs => enter [1]; rw [mul_comm, ←Polynomial.eval_C_mul]
      conv_lhs => enter [2]; rw [mul_comm, ←Polynomial.eval_C_mul]
      -- ⊢ eval y (C (1-r) * ∑...) + eval y (C r * ∑...) = eval y (∑...)
      rw [←Polynomial.eval_add]
      -- ⊢ poly_left.eval y = poly_right.eval y
      congr
      simp_rw [mul_sum, ←Finset.sum_add_distrib]
      -- We now prove that the terms inside the sums are equal for each index.
      apply Finset.sum_congr rfl
      intro j hj
      have h_j_lt : j.val < 2 ^ (ℓ - (↑i + 1)) := by
        rw [Nat.sub_add_eq]
        omega
      conv_lhs => enter [1]; rw [mul_comm (a := Polynomial.C (coeffs ⟨j.val * 2, by
        rw [←Nat.add_zero (j.val * 2)]
        apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
          (i := 0) (by omega) (by omega)⟩)), ←mul_assoc,
        mul_comm (a := Polynomial.C (1 - r_chal))]; rw [mul_assoc]
      conv_lhs => enter [2]; rw [mul_comm (a := Polynomial.C (coeffs ⟨j.val * 2 + 1, by
        apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
          (i := 1) (by omega) (by omega)⟩)), ←mul_assoc,
        mul_comm (a := Polynomial.C r_chal)]; rw [mul_assoc]
      conv_rhs => rw [mul_comm]
      rw [←mul_add]
      congr
      simp only [←Polynomial.C_mul, ←Polynomial.C_add]
