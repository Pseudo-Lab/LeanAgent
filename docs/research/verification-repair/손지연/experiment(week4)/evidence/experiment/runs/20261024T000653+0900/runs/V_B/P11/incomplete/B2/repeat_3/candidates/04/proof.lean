by
  classical
  dsimp only
  intro y
  let evenIndex : Fin (2 ^ (ℓ - (i + 1))) → Fin (2 ^ (ℓ - i)) := fun j =>
    ⟨j.val * 2, by
      rw [← Nat.add_zero (j.val * 2)]
      exact mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j)
        (b := ℓ - (↑i + 1)) (i := 0) (by omega) (by omega)⟩
  let oddIndex : Fin (2 ^ (ℓ - (i + 1))) → Fin (2 ^ (ℓ - i)) := fun j =>
    ⟨j.val * 2 + 1, by
      exact mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j)
        (b := ℓ - (↑i + 1)) (i := 1) (by omega) (by omega)⟩
  have hn : ℓ - i = (ℓ - (i + 1)) + 1 := by omega
  let pairEquiv :
      Fin (2 ^ (ℓ - (i + 1))) × Fin 2 ≃ Fin (2 ^ (ℓ - i)) :=
    { toFun := fun p => ⟨p.1.val * 2 + p.2.val, by
        exact mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := p.1)
          (b := ℓ - (↑i + 1)) (i := p.2.val) (by omega) (by omega)⟩
      invFun := fun k =>
        (⟨k.val / 2, by
            have hk := k.isLt
            rw [hn, pow_succ] at hk
            omega⟩,
         ⟨k.val % 2, Nat.mod_lt _ (by omega)⟩)
      left_inv := by
        rintro ⟨j, b⟩
        apply Prod.ext
        · apply Fin.ext
          simp only
          omega
        · apply Fin.ext
          simp only
          omega
      right_inv := by
        intro k
        apply Fin.ext
        simp only
        omega }
  have split_sum (F : Fin (2 ^ (ℓ - i)) → L[X]) :
      (∑ x, F x) =
        ∑ j : Fin (2 ^ (ℓ - (i + 1))), (F (evenIndex j) + F (oddIndex j)) := by
    calc
      (∑ x, F x) = ∑ p : Fin (2 ^ (ℓ - (i + 1))) × Fin 2, F (pairEquiv p) :=
        (pairEquiv.sum_comp F).symm
      _ = ∑ j : Fin (2 ^ (ℓ - (i + 1))),
          ∑ b : Fin 2, F (pairEquiv (j, b)) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ j : Fin (2 ^ (ℓ - (i + 1))),
          (F (evenIndex j) + F (oddIndex j)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Fin.sum_univ_two]
            simp [pairEquiv, evenIndex, oddIndex]
  simp only [fold]
  simp_rw [qMap_total_fiber_one_level_eq 𝔽q β i (by omega)]
  simp only [intermediateEvaluationPoly]
  simp_rw [split_sum]
  simp [Fin2ToF2, intermediateNovelBasisX, intermediateNormVpoly,
    Fin.prod_univ_succ, evenIndex, oddIndex] <;> ring_nf