by
  have h := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at h
  · rw [Continuous.ae_eq_iff_eq] at h
    · funext x
      simpa using congrFun h x
    · have hc : Continuous f := hf.smooth.continuous
      exact Continuous.inner' f f hc hc
    · exact continuous_const
  · intro x
    exact real_inner_self_nonneg' (f x)
  · exact IsTestFunction.integrable (IsTestFunction.inner hf hf)