by
  classical
  fail_if_success
    rw [timeOrderF_superCommuteF_ofCrAnOpF_ofCrAnOpF_eq_time hφψ hψφ]
  guard_target =
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * b) =
      ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * b))
  exact ι_timeOrderF_superCommuteF_eq_time hφψ hψφ a b