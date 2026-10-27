by
  funext x₀
  by_contra hx₀
  have hpos : 0 < ⟪f x₀, f x₀⟫_ℝ := real_inner_self_pos'.2 hx₀
  have hopen : IsOpen {x : Y | 0 < ⟪f x, f x₀⟫_ℝ} := by
    apply isOpen_lt continuous_const
    fun_prop
  have hxmem : x₀ ∈ {x : Y | 0 < ⟪f x, f x₀⟫_ℝ} := by
    simpa using hpos
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.1 hopen) x₀ hxmem
  let b : ContDiffBump x₀ :=
    (ContDiffBump.ofInnerProductSpace x₀).rescale ε hε
  let g : Y → V := fun x => b x • f x₀
  have hg_test : IsTestFunction g := by
    constructor
    · fun_prop
    · simpa [g] using
        b.hasCompactSupport.smul_right (fun _ : Y => f x₀)
  have hzero := hg g hg_test
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at hzero
  · rw [Continuous.ae_eq_iff_eq] at hzero
    · have hzero_x := congrFun hzero x₀
      have hinner : ⟪f x₀, f x₀⟫_ℝ = 0 := by
        simpa [g, b] using hzero_x
      exact hx₀ (by simpa using hinner)
    · fun_prop
    · fun_prop
  · intro x
    simp only [g, real_inner_smul_right]
    by_cases hbx : b x = 0
    · simp [hbx]
    · have hxs : x ∈ Function.support (b : Y → ℝ) := hbx
      have hxball : x ∈ Metric.ball x₀ ε := by
        simpa [b] using b.support hxs
      exact mul_nonneg (b.nonneg x) (le_of_lt (hball hxball))
  · apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · have hc :=
        b.hasCompactSupport.mul_right (fun x : Y => ⟪f x, f x₀⟫_ℝ)
      simpa [g, real_inner_smul_right] using hc