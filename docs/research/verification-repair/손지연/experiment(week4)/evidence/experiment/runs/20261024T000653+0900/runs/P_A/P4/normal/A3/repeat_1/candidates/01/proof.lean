by
  have h : (fun x => ⟪f x, f x⟫_ℝ) =ᵐ[μ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun x => real_inner_self_nonneg' (f x))
      (IsTestFunction.inner hf hf).integrable).mp (hg f hf)
  have h' : (fun x => ⟪f x, f x⟫_ℝ) = 0 :=
    (Continuous.ae_eq_iff_eq
      (IsTestFunction.inner hf hf).smooth.continuous continuous_const).mp h
  funext x
  simpa using congrFun h' x