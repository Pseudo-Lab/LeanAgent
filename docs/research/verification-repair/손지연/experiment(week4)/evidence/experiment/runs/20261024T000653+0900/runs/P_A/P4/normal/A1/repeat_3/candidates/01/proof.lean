by
  have h := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at h
  · rw [Continuous.ae_eq_iff_eq] at h
    · funext x
      simpa using congrFun h x
    · exact (IsTestFunction.inner hf hf).smooth.continuous
    · exact continuous_const
  · exact fun x => real_inner_self_nonneg' (f x)
  · exact (IsTestFunction.inner hf hf).integrable