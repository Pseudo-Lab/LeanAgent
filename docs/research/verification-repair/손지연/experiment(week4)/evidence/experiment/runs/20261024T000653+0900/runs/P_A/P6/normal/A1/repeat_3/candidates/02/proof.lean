by
  have ha (φs : List 𝓕.CrAnFieldOp) (a : 𝓕.FieldOpFreeAlgebra) :
      ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * ofCrAnListF φs) =
      ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * ofCrAnListF φs)) := by
    let pa (a : 𝓕.FieldOpFreeAlgebra)
        (_ : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) : Prop :=
      ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * ofCrAnListF φs) =
      ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * ofCrAnListF φs))
    change pa a (Basis.mem_span _ a)
    apply Submodule.span_induction
    · rintro x ⟨φs', rfl⟩
      simpa only [ofListBasis_eq_ofList, pa] using
        ι_timeOrderF_superCommuteF_eq_time hφψ hψφ
          (ofCrAnListF φs') (ofCrAnListF φs)
    · simp [pa]
    · intro x y hx hy hpx hpy
      simp_all [pa, add_mul]
    · intro x hx hpx
      simp_all [pa]
  let pb (b : 𝓕.FieldOpFreeAlgebra)
      (_ : b ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) : Prop :=
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * b) =
    ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * b))
  change pb b (Basis.mem_span _ b)
  apply Submodule.span_induction
  · rintro x ⟨φs, rfl⟩
    simpa only [ofListBasis_eq_ofList, pb] using ha φs a
  · simp [pb]
  · intro x y hx hy hpx hpy
    simp_all [pb, mul_add]
  · intro x hx hpx
    simp_all [pb]