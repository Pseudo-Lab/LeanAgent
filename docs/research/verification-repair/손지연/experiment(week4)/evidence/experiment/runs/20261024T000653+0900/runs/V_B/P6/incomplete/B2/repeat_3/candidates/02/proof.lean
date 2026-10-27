by
  classical
  let p (a : 𝓕.FieldOpFreeAlgebra)
      (ha : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) : Prop :=
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * b) =
      ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * b))
  change p a (Basis.mem_span _ a)
  apply Submodule.span_induction
  · rintro x ⟨φs, rfl⟩
    simp only [ofListBasis_eq_ofList, p]
    revert b
    induction φs using List.reverseRecOn with
    | nil =>
        intro b
        simp only [ofCrAnListF_nil, one_mul]
        rw [timeOrderF_timeOrderF_mid]
        rw [timeOrderF_superCommuteF_ofCrAnOpF_ofCrAnOpF_eq_time hφψ hψφ]
    | append_singleton φs χ ih =>
        intro b
        have hn := ι_timeOrderF_superCommuteF_superCommuteF
          (φ1 := χ) (φ2 := φ) (φ3 := ψ) (ofCrAnListF φs) b
        have hi := ih (ofCrAnOpF χ * b)
        by_cases hs : 𝓕.crAnStatistics φ = 𝓕.crAnStatistics ψ
        · simp_all [ofCrAnListF_append, superCommuteF, mul_assoc, mul_add, add_mul]
        · simp_all [ofCrAnListF_append, superCommuteF, mul_assoc, mul_add, add_mul,
            map_mul, ι_superCommuteF_of_diff_statistic hs]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all [p, add_mul, mul_add]
  · intro x hx hpx
    simp_all [p]