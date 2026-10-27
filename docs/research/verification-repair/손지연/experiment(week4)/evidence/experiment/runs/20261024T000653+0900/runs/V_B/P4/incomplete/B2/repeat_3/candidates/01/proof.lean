by
  funext y
  by_contra hy
  have hcont : Continuous (fun x => ⟪f x, f y⟫_ℝ) := by
    fun_prop
  have hypos : 0 < ⟪f y, f y⟫_ℝ := real_inner_self_pos'.mpr hy
  have hopen : IsOpen ((fun x => ⟪f x, f y⟫_ℝ) ⁻¹' Set.Ioi 0) :=
    isOpen_Ioi.preimage hcont
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen y hypos
  let b : ContDiffBump y :=
    ContDiffBump.ofInnerProductSpace y (ε / 2) (ε / 2)
      (half_pos hε) (half_pos hε)
  have hbcomp : HasCompactSupport (b : Y → ℝ) := b.hasCompactSupport
  have hbtest : IsTestFunction (fun x => b x • f y) := by
    constructor
    · exact b.contDiff.smul contDiff_const
    · apply hbcomp.mono
      intro x hx
      change b x • f y ≠ 0 at hx
      change b x ≠ 0
      intro hbx
      simp [hbx] at hx
  have hnonneg : ∀ x, 0 ≤ ⟪f x, b x • f y⟫_ℝ := by
    intro x
    by_cases hbx : b x = 0
    · simp [hbx]
    · have hxball' : x ∈ Metric.ball y b.rOut := by
        by_contra hx
        exact hbx (b.zero_of_not_mem_ball hx)
      have hxball : x ∈ Metric.ball y ε := by
        convert hxball' using 1 <;> dsimp [b] <;> ring
      rw [real_inner_smul_right]
      exact mul_nonneg (b.nonneg x) (le_of_lt (hεsub hxball))
  have hint_cont : Continuous (fun x => ⟪f x, b x • f y⟫_ℝ) := by
    fun_prop
  have hint_comp : HasCompactSupport (fun x => ⟪f x, b x • f y⟫_ℝ) := by
    apply hbcomp.mono
    intro x hx
    change ⟪f x, b x • f y⟫_ℝ ≠ 0 at hx
    change b x ≠ 0
    intro hbx
    simp [hbx] at hx
  have hzero := hg (fun x => b x • f y) hbtest
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at hzero
  · rw [Continuous.ae_eq_iff_eq] at hzero
    · apply hy
      have hyzero := congrFun hzero y
      simpa [b] using hyzero
    · exact hint_cont
    · fun_prop
  · exact hnonneg
  · exact hint_cont.integrable_of_hasCompactSupport hint_comp