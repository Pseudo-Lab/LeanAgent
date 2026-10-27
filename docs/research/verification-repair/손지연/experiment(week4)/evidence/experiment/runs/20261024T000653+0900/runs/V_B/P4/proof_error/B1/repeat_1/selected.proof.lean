by
  rw [funext_iff]
  by_contra h₀
  obtain ⟨x₀, hx0⟩ := not_forall.1 h₀
  simp at hx0
  let f₂ : Y → WithLp 2 V := toL2 ℝ ∘ f
  let x₂ := f₂ x₀
  have hx2 : x₂ ≠ 0 := by
    intro h
    apply hx0
    exact congrArg (fromL2 ℝ) h
  have hcont₂ : ContinuousAt f₂ x₀ := ((toL2 ℝ).continuous.comp hf).continuousAt
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=
    Metric.continuousAt_iff.mp hcont₂ (‖x₂‖ / 2)
      (by simpa [half_pos] using (norm_pos_iff.mpr hx2))
  have inner_pos₂ : ∀ x (hx : x ∈ Metric.ball x₀ δ₂), 0 < (⟪f₂ x, x₂⟫_ℝ : ℝ) := by
    intros x hx
    have hclose : ‖f₂ x - x₂‖ < ‖x₂‖ / 2 := by
      convert hδ₂ hx using 1
      simp [x₂, dist_eq_norm]
    have hself : ⟪x₂, x₂⟫_ℝ = ‖x₂‖^2 :=
      real_inner_self_eq_norm_sq (x₂ : WithLp 2 V)
    have hcs : -(‖f₂ x - x₂‖ * ‖x₂‖) ≤ ⟪f₂ x - x₂, x₂⟫_ℝ :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have hxp : 0 < ‖x₂‖ := norm_pos_iff.mpr hx2
    have inner_eq_self_add_diff :
        ⟪f₂ x, x₂⟫_ℝ = ⟪x₂, x₂⟫_ℝ + ⟪f₂ x - x₂, x₂⟫_ℝ := by
      rw [← inner_add_left]
      simp
    nlinarith [inner_eq_self_add_diff, hcs, hself, hclose, hxp,
      mul_lt_mul_of_pos_right hclose hxp]
  have inner_pos_V : ∀ x ∈ Metric.ball x₀ δ₂, 0 < ⟪f x, f x₀⟫_ℝ :=
    fun x hx => inner_pos₂ x hx
  have bump_exists : ∃ φ : Y → ℝ, IsTestFunction φ ∧ φ x₀ > 0 ∧
      (∀ x ∈ Function.support φ, 0 ≤ φ x) ∧
      Function.support φ ⊆ Metric.ball x₀ (δ₂ / 2) ∧
      (∀ x ∈ Metric.closedBall x₀ (δ₂ / 4), 0 < φ x) := by
    haveI : HasContDiffBump Y := hasContDiffBump_of_innerProductSpace Y
    let φ1 : ContDiffBump x₀ :=
      ⟨δ₂ / 4, δ₂ / 2, by positivity, by linarith⟩
    refine ⟨φ1.toFun, ⟨φ1.contDiff, φ1.hasCompactSupport⟩,
      φ1.pos_of_mem_ball (Metric.mem_ball_self φ1.rOut_pos),
      fun x _ => φ1.nonneg, by rw [ContDiffBump.support_eq],
      fun x hx => φ1.pos_of_mem_ball ?_⟩
    rw [Metric.mem_closedBall] at hx
    exact Metric.mem_ball.mpr
      (lt_of_le_of_lt hx (by show δ₂ / 4 < δ₂ / 2; linarith))
  obtain ⟨φ, hφ_testfun, hφ_pos_x₀, hφ_non_neg, hφ_support_subset,
    hφ_pos_inner⟩ := bump_exists
  let g : Y → V := fun x => φ x • f x₀
  have hg_test : IsTestFunction g :=
    IsTestFunction.smul_right hφ_testfun contDiff_const
  have key_integral := hg g hg_test
  simp only [g, inner_smul_right'] at key_integral
  have support_subset : Function.support φ ⊆ Metric.ball x₀ δ₂ :=
    hφ_support_subset.trans (Metric.ball_subset_ball (by linarith))
  have supp_subset2 :
      Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) ⊆
        Function.support φ := by
    intro x hprod hφ0
    simp [hφ0] at hprod
  have hinner_cont : Continuous (fun x => ⟪f x, f x₀⟫_ℝ) :=
    Continuous.inner' (f : Y → V) (fun _ => f x₀) hf continuous_const
  have integrable_prod :
      Integrable (fun x => φ x * ⟪f x, f x₀⟫_ℝ) μ :=
    (Continuous.mul hφ_testfun.smooth.continuous hinner_cont).integrable_of_hasCompactSupport
      (hφ_testfun.supp.mono supp_subset2)
  have h_nonneg : ∀ x, 0 ≤ φ x * ⟪f x, f x₀⟫_ℝ := by
    intro x
    by_cases hx : x ∈ Function.support φ
    · exact mul_nonneg (hφ_non_neg x hx) (inner_pos_V x (support_subset hx)).le
    · simp [Function.notMem_support.mp hx]
  have hμ_ball : 0 < μ (Metric.ball x₀ (δ₂ / 4)) :=
    Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr (by linarith))
  have hμ : 0 < μ (Metric.closedBall x₀ (δ₂ / 4)) :=
    lt_of_lt_of_le hμ_ball (measure_mono Metric.ball_subset_closedBall)
  have closedBall_subset_support :
      Metric.closedBall x₀ (δ₂ / 4) ⊆
        Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) := by
    intro x hx
    have hφx := hφ_pos_inner x hx
    have hin : 0 < ⟪f x, f x₀⟫_ℝ :=
      inner_pos_V x (Metric.closedBall_subset_ball (by linarith) hx)
    simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq]
    constructor
    · linarith
    · linarith
  have integral_pos : 0 < ∫ x, φ x * ⟪f x, f x₀⟫_ℝ ∂μ :=
    (integral_pos_iff_support_of_nonneg h_nonneg integrable_prod).mpr
      (lt_of_lt_of_le hμ (measure_mono closedBall_subset_support))
  linarith