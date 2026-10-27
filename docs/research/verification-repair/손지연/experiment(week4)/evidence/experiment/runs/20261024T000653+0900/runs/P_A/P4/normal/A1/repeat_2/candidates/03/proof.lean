by
  have h := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at h
  · rw [Continuous.ae_eq_iff_eq] at h
    · apply funext
      intro x
      simpa using congrFun h x
    · exact (hf.inner hf).smooth.continuous
    · exact continuous_const
  · intro x
    simpa only [Pi.zero_apply] using real_inner_self_nonneg' (f x)
  · exact (hf.inner hf).integrable