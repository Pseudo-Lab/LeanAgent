by
  simp only
  intro y
  set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := 1)
    (h_i_add_steps := by simp only; omega) (y := y)
  set x₀ := fiberMap 0
  set x₁ := fiberMap 1
  set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) coeffs
  set new_coeffs := fun j : Fin (2 ^ (ℓ - (i + 1))) =>
    (1 - r_chal) * coeffs ⟨j.val * 2, by
      rw [← Nat.add_zero (j.val * 2)]
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j)
        (b := ℓ - (↑i + 1)) (i := 0) <;> omega⟩ +
    r_chal * coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j)
        (b := ℓ - (↑i + 1)) (i := 1) <;> omega⟩
  set P_i_plus_1 := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i + 1, by omega⟩) new_coeffs

  have h_eval_qMap (k : Fin 2) :
      (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval (fiberMap k).val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate
      i (by omega) (fiberMap k)
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    have hk := is_fiber_iff_generates_quotient_point 𝔽q β i
      (steps := 1) (by omega) (x := fiberMap k) (y := y) |>.mpr (by
        rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [hk]
  have h_eval_qMap_x₀ :
      (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₀.val = y := by
    simpa only [x₀] using h_eval_qMap (0 : Fin 2)
  have h_eval_qMap_x₁ :
      (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₁.val = y := by
    simpa only [x₁] using h_eval_qMap (1 : Fin 2)

  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
    (by simp only; omega)
  let y_lifted : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ :=
    sDomain.lift 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (j := ⟨i + 1, by omega⟩)
      (h_j := by omega) (h_le := by apply Fin.mk_le_mk.mpr; omega) y
  have hx₀ : x₀ = y_lifted := by
    simpa [x₀, fiberMap, basis_x, y_lifted, Fin2ToF2] using
      (qMap_total_fiber_one_level_eq 𝔽q β i (by omega) y (0 : Fin 2))
  have hx₁ : x₁ = basis_x ⟨0, by omega⟩ + y_lifted := by
    simpa [x₁, fiberMap, basis_x, y_lifted, Fin2ToF2] using
      (qMap_total_fiber_one_level_eq 𝔽q β i (by omega) y (1 : Fin 2))
  have h_fiber_diff : x₁.val - x₀.val = 1 := by
    rw [hx₁, hx₀]
    change (basis_x ⟨0, by omega⟩ : L) + (y_lifted : L) - (y_lifted : L) = 1
    rw [add_sub_cancel_right]
    simp only [basis_x, get_sDomain_basis, Fin.coe_ofNat_eq_mod, zero_mod,
      add_zero, cast_eq]
    rw [normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β]

  set P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  set P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  have h_P_i_eval := evaluation_poly_split_identity 𝔽q β
    h_ℓ_add_R_rate ⟨i, by omega⟩ coeffs
  have h_equation_39
      (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩)
      (hx : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x.val = y) :
      P_i.eval x.val = P₀.eval y.val + x.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Fin.eta, Polynomial.eval_add, eval_comp, hx,
      Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  have h_equation_39_x₀ := h_equation_39 x₀ h_eval_qMap_x₀
  have h_equation_39_x₁ := h_equation_39 x₁ h_eval_qMap_x₁

  have h_next_poly :
      P_i_plus_1 = Polynomial.C (1 - r_chal) * P₀ + Polynomial.C r_chal * P₁ := by
    simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement,
      oddRefinement, intermediateEvaluationPoly]
    simp_rw [mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Polynomial.C_add, Polynomial.C_mul]
    ring

  set f_i := fun (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩) =>
    P_i.eval x.val
  set f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := by omega)
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
      simp only [h_next_poly, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C]
      ring