by
  have h_integral := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at h_integral
  · rw [Continuous.ae_eq_iff_eq] at h_integral
    · funext x
      have hx := congrFun h_integral x
      simpa using hx
    · exact hf.smooth.continuous.inner hf.smooth.continuous
    · fun_prop
  · intro x
    simp only [Pi.zero_apply]
    exact real_inner_self_nonneg' (f x)
  · exact (IsTestFunction.inner hf hf).integrable