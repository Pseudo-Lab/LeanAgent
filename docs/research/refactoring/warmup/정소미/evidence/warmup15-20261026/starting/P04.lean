lemma fundamental_theorem_of_variational_calculus' {f : Y → V}
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [OpensMeasurableSpace Y]
    (hf : Continuous f) (hg : ∀ g, IsTestFunction g → ∫ x, ⟪f x, g x⟫_ℝ ∂μ = 0) :
    f = 0 := by
  funext x
  have hle := ‹OpensMeasurableSpace Y›.borel_le
  have hc := hf.inner' (𝕜 := ℝ) f (fun _ => f x) continuous_const
  refine inner_self_eq_zero'.1 (congrFun ((hc.ae_eq_iff_eq μ continuous_zero).1
    (ae_eq_of_ae_eq_trim (hm := hle) ?_)) x)
  letI := borel Y
  haveI : BorelSpace Y := ⟨rfl⟩
  haveI : IsFiniteMeasureOnCompacts (μ.trim hle) := ⟨fun K hK =>
    trim_measurableSet_eq hle hK.measurableSet ▸ hK.measure_lt_top⟩
  exact ae_eq_zero_of_integral_contDiff_smul_eq_zero hc.locallyIntegrable fun g hgs hgc =>
    (integral_trim hle (hgs.continuous.mul hc).stronglyMeasurable).symm.trans
      (by simpa only [inner_smul_right', Pi.mul_apply] using
        hg _ (.smul_right ⟨hgs, hgc⟩ contDiff_const))
