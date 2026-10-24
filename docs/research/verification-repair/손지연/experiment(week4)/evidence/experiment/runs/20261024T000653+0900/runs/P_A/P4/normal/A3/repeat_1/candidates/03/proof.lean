by
  have h := (MeasureTheory.integral_eq_zero_iff_of_nonneg
    (fun _ => real_inner_self_nonneg') (hf.inner hf).integrable).mp (hg f hf)
  have h := (Continuous.ae_eq_iff_eq
    (hf.inner hf).smooth.continuous continuous_const).mp h
  funext x
  simpa using congrFun h x