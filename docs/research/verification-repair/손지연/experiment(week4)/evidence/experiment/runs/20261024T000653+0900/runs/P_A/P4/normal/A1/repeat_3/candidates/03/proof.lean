by
  have h := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at h
  · rw [Continuous.ae_eq_iff_eq] at h
    · ext x
      simpa using congrFun h x
    · fun_prop
    · fun_prop
  · exact fun x => real_inner_self_nonneg'
  · exact (hf.inner hf).integrable