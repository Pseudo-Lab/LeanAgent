by
  have h := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at h
  · rw [Continuous.ae_eq_iff_eq] at h
    · exact funext fun x => by simpa using congrFun h x
    · exact (hf.inner hf).smooth.continuous
    · exact continuous_zero
  · intro x
    simp only [Pi.zero_apply]
    apply real_inner_self_nonneg'
  · exact (hf.inner hf).integrable