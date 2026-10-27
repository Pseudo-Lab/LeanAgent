by
  have h := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at h
  · rw [Continuous.ae_eq_iff_eq] at h
    · funext x
      simpa using congrFun h x
    · exact (IsTestFunction.inner hf hf).smooth.continuous
    · exact continuous_zero
  · exact fun _ => real_inner_self_nonneg'
  · exact IsTestFunction.integrable (IsTestFunction.inner hf hf)