by
  have hfc : Continuous f := hf.smooth.continuous
  have h := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at h
  · rw [Continuous.ae_eq_iff_eq] at h
    · funext x
      have hx := congrFun h x
      simpa using hx
    · fun_prop
    · fun_prop
  · exact fun x => real_inner_self_nonneg' _
  · exact (hf.inner hf).integrable