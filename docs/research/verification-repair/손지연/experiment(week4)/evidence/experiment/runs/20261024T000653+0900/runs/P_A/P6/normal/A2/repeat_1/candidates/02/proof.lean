by
  let pb (b : 𝓕.FieldOpFreeAlgebra)
      (hc : b ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) : Prop :=
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * b) =
      ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * b))
  change pb b (Basis.mem_span _ b)
  apply Submodule.span_induction
  · rintro x ⟨φs, rfl⟩
    simp only [ofListBasis_eq_ofList, map_mul, pb]
    let pa (a : 𝓕.FieldOpFreeAlgebra)
        (hc : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) : Prop :=
      ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * ofCrAnListF φs) =
        ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * ofCrAnListF φs))
    change pa a (Basis.mem_span _ a)
    apply Submodule.span_induction
    · rintro x ⟨φs', rfl⟩
      simp only [ofListBasis_eq_ofList, map_mul, pa]
      let l0 := List.takeWhile (fun c => ¬ crAnTimeOrderRel φ c)
        (List.insertionSort crAnTimeOrderRel (φs' ++ φs))
      let l1 := List.filter
        (fun c => crAnTimeOrderRel φ c ∧ crAnTimeOrderRel c φ) φs'
      let l2 := List.filter
        (fun c => crAnTimeOrderRel φ c ∧ crAnTimeOrderRel c φ) φs
      let l3 := List.filter
        (fun c => crAnTimeOrderRel φ c ∧ ¬ crAnTimeOrderRel c φ)
        (List.insertionSort crAnTimeOrderRel (φs' ++ φs))
      calc _
        _ = crAnTimeOrderSign (φs' ++ φ :: ψ :: φs) •
            ι (ofCrAnListF (crAnTimeOrderList (φs' ++ φ :: ψ :: φs))) -
          crAnTimeOrderSign (φs' ++ ψ :: φ :: φs) •
            𝓢(𝓕.crAnStatistics φ, 𝓕.crAnStatistics ψ) •
              ι (ofCrAnListF (crAnTimeOrderList (φs' ++ ψ :: φ :: φs))) := by
          conv_lhs =>
            rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton,
              superCommuteF_ofCrAnListF_ofCrAnListF]
            simp [mul_sub, sub_mul, ← ofCrAnListF_append]
            rw [timeOrderF_ofCrAnListF, timeOrderF_ofCrAnListF]
          simp only [map_smul, sub_right_inj]
          module
        _ = crAnTimeOrderSign (φs' ++ φ :: ψ :: φs) •
            (ι (ofCrAnListF (crAnTimeOrderList (φs' ++ φ :: ψ :: φs))) -
            𝓢(𝓕.crAnStatistics φ, 𝓕.crAnStatistics ψ) •
              ι (ofCrAnListF (crAnTimeOrderList (φs' ++ ψ :: φ :: φs)))) := by
          rw [crAnTimeOrderSign_swap_eq_time hφψ hψφ]
          module
        _ = crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs) •
            (ι (ofCrAnListF l0) * ι (ofCrAnListF l1) *
              ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF *
              ι (ofCrAnListF l2) * ι (ofCrAnListF l3)) := by
          have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ φs' [φ, ψ] φs
            (by simp_all)
          rw [crAnTimeOrderList,
            show φs' ++ φ :: ψ :: φs = φs' ++ [φ, ψ] ++ φs by simp, h1]
          have h2 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ φs' [ψ, φ] φs
            (by simp_all)
          rw [crAnTimeOrderList,
            show φs' ++ ψ :: φ :: φs = φs' ++ [ψ, φ] ++ φs by simp, h2]
          repeat rw [ofCrAnListF_append]
          rw [superCommuteF_ofCrAnOpF_ofCrAnOpF, ← ofCrAnListF_singleton,
            ← ofCrAnListF_singleton]
          simp [l0, l1, l2, l3, ← ofCrAnListF_append, mul_sub, sub_mul]
      rw [Subalgebra.mem_center_iff.mp
        (ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_mem_center φ ψ)]
      repeat rw [mul_assoc]
      rw [← map_mul, ← map_mul, ← map_mul, ← ofCrAnListF_append,
        ← ofCrAnListF_append, ← ofCrAnListF_append]
      have h1 := insertionSort_of_takeWhile_filter 𝓕.crAnTimeOrderRel φ φs' φs
      simp [l0, l1, l2, l3, decide_not, Bool.decide_and, List.append_assoc,
        List.cons_append] at h1 ⊢
      rw [← h1, ← crAnTimeOrderList]
      by_cases hq : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)
      · simp [ι_superCommuteF_of_diff_statistic hq]
      · rw [crAnTimeOrderSign,
          Wick.koszulSign_eq_rel_eq_stat _ _ hφψ hψφ (by simp_all),
          ← crAnTimeOrderSign, ← ofCrAnListF_append, timeOrderF_ofCrAnListF]
        simp only [map_smul, Algebra.mul_smul_comm]
    · simp only [map_mul, zero_mul, map_zero, mul_zero, pa]
    · intro x y hx hy hpx hpy
      simp_all [pa, mul_add, add_mul]
    · intro x hx hpx
      simp_all [pa]
  · simp only [map_mul, mul_zero, map_zero, pb]
  · intro x y hx hy hpx hpy
    simp_all [pb, mul_add]
  · intro x hx hpx
    simp_all [pb]