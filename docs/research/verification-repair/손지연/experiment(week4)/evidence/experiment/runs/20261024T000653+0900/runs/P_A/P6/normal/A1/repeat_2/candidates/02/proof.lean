by
  let pa (a : 𝓕.FieldOpFreeAlgebra)
      (_ : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) : Prop :=
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * b) =
      ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * b))
  change pa a (Basis.mem_span _ a)
  apply Submodule.span_induction
  · rintro x ⟨φs', rfl⟩
    simp only [ofListBasis_eq_ofList, map_mul, pa]
    let pb (b : 𝓕.FieldOpFreeAlgebra)
        (_ : b ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) : Prop :=
      ι 𝓣ᶠ(ofCrAnListF φs' * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * b) =
        ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(ofCrAnListF φs' * b))
    change pb b (Basis.mem_span _ b)
    apply Submodule.span_induction
    · rintro x ⟨φs, rfl⟩
      simpa only [ofListBasis_eq_ofList, pb] using
        ι_timeOrderF_superCommuteF_eq_time hφψ hψφ (ofCrAnListF φs') (ofCrAnListF φs)
    · simp [pb]
    · rintro x y _ _ hx hy
      simp_all [pb, mul_add]
    · rintro x _ hx
      simp_all [pb]
  · simp [pa]
  · rintro x y _ _ hx hy
    simp_all [pa, add_mul]
  · rintro x _ hx
    simp_all [pa]