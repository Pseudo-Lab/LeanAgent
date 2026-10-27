by
  have h := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at h
  · rw [Continuous.ae_eq_iff_eq] at h
    · funext x
      simpa using congrFun h x
    · exact Continuous.inner' f f hf.smooth.continuous hf.smooth.continuous
    · exact continuous_const
  · exact fun x => real_inner_self_nonneg'
  · exact (hf.inner hf).integrable