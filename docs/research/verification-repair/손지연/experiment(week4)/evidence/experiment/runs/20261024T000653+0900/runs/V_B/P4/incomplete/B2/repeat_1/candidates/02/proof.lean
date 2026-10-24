by
  have hf' := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at hf'
  · rw [Continuous.ae_eq_iff_eq] at hf'
    · funext x
      have hf'' := congrFun hf' x
      simpa using hf''
    · exact hf.smooth.continuous.inner hf.smooth.continuous
    · fun_prop
  · intro x
    simp only [Pi.zero_apply]
    exact real_inner_self_nonneg'
  · exact (IsTestFunction.inner hf hf).integrable