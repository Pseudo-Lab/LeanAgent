by
  classical
  simp only
  intro y
  have h₀ := qMap_total_fiber_one_level_eq 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (by omega) y (0 : Fin 2)
  have h₁ := qMap_total_fiber_one_level_eq 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (by omega) y (1 : Fin 2)
  simp only at h₀ h₁
  simp only [fold]
  rw [h₀, h₁]
  have hsub : ℓ - i.val = (ℓ - (i.val + 1)) + 1 := by
    omega
  have hpow :
      2 ^ (ℓ - i.val) = 2 ^ (ℓ - (i.val + 1)) * 2 := by
    rw [hsub, pow_succ]
  let encode :
      Fin (2 ^ (ℓ - (i.val + 1))) × Fin 2 → Fin (2 ^ (ℓ - i.val)) :=
    fun p => ⟨p.1.val * 2 + p.2.val, by rw [hpow]; omega⟩
  have hencode : Function.Bijective encode := by
    constructor
    · intro a b hab
      have hv := congrArg Fin.val hab
      change a.1.val * 2 + a.2.val = b.1.val * 2 + b.2.val at hv
      have ha := a.2.isLt
      have hb := b.2.isLt
      apply Prod.ext
      · apply Fin.ext
        omega
      · apply Fin.ext
        omega
    · intro k
      have hk := k.isLt
      have hdiv : k.val / 2 < 2 ^ (ℓ - (i.val + 1)) := by
        rw [hpow] at hk
        omega
      refine ⟨(⟨k.val / 2, hdiv⟩, ⟨k.val % 2, by omega⟩), ?_⟩
      apply Fin.ext
      change (k.val / 2) * 2 + k.val % 2 = k.val
      exact Nat.div_add_mod k.val 2
  let e :
      Fin (2 ^ (ℓ - (i.val + 1))) × Fin 2 ≃ Fin (2 ^ (ℓ - i.val)) :=
    Equiv.ofBijective encode hencode
  have hsum (f : Fin (2 ^ (ℓ - i.val)) → L) :
      ∑ x, f x =
        ∑ j : Fin (2 ^ (ℓ - (i.val + 1))),
          (f ⟨j.val * 2, by rw [hpow]; omega⟩ +
            f ⟨j.val * 2 + 1, by rw [hpow]; omega⟩) := by
    calc
      ∑ x, f x = ∑ p, f (e p) := (e.sum_comp f).symm
      _ = ∑ j : Fin (2 ^ (ℓ - (i.val + 1))),
          (f ⟨j.val * 2, by rw [hpow]; omega⟩ +
            f ⟨j.val * 2 + 1, by rw [hpow]; omega⟩) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro j _
        simp [Fin.sum_univ_two, e, encode]
  simp [Fin2ToF2, intermediateEvaluationPoly, intermediateNovelBasisX,
    hsum, hsub, pow_succ, h_β₀_eq_1.out,
    Submodule.coe_add, Submodule.coe_smul] <;> ring