/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.VariationalCalculus.IsTestFunction
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
/-!

# Fundamental lemma of the calculus of variations

The key took in variational calculus is:
```
∀ h, ∫ x, f x * h x = 0 → f = 0
```
which allows use to go from reasoning about integrals to reasoning about functions.

## Overview of variational calculus

The variational calculus API in Physlib is designed to match and formalize the physicists intuition
of variational calculus. It is not designed to be a general API for variational calculus.

Within variational caclulus we are interested in function transformations, `F : (X → U) → (Y → V)`.
In physics this functional is often of the form `L : (Time → U) → Time → ℝ`,
which represents the Lagrangian of a system. We will use this to explain the formalization
within this API.

The action is nominally given by
$$S[u] = \int L(u, t) dt,$$
however it is convenient to
introduce another function `φ` and define the action as
$$S[u] = \int φ(t) L(u, t) dt.$$
In the end we will set `φ := fun _ => 1`.

We now consider $$\frac{\partial}{\partial s} S[u + s * \delta u]$$ at `s = 0`,
which is the variational derivative of `S` at `u` in the direction `δu`.
This is equal to
$$
\int φ(t) * \left. \frac{\partial}{\partial s} L(u + s * \delta u, t)\right|_{s = 0}dt
$$
Let us denote the function
$$
\delta u,\, t \mapsto \left. \frac{\partial}{\partial s} L(u + s * \delta u, t)\right|_{s = 0}
$$ as `Lᵤ : (Time → U) → (Time → ℝ)`.
Then the variational derivative is
$$\int φ (t) Lᵤ(δu, t) dt.$$

It may then be possible to find a function `Gᵤ : (Time → ℝ) → Time → U`
such that
$$
\int φ(t) Lᵤ(δu, t) dt = \int \langle Gᵤ(φ, t), δu(t)\rangle dt
$$
This is usually done by integration by parts.

We now set `φ := fun _ => 1` and get `grad u := Gᵤ (fun _ => 1)`, which is the
variational gradient at `u`. The Euler–Lagrange equations, for example, are then `grad u = 0`.

In our API, the relationship between
- `Lᵤ` and `Gᵤ` is captured by the `HasVarAdjoint`.
- `L` and `Gᵤ` by `HasVarAdjDeriv`.
- `L` and `grad u` by `HasVarGradientAt`.

In practice we assume that `L` has a certain locality property
`IsLocalizedFunctionTransform`, which allows us to work with functions
`φ` and `δu` which have compact support.

This API assumes that `U` is an inner-product space. This can be considered as the full
configuration space, or a local chart thereof.

## References

- https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/Variational.20Calculus/with/529022834

-/

@[expose] public section

open MeasureTheory InnerProductSpace InnerProductSpace'

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {V} [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace' ℝ V]
  {Y} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y][MeasurableSpace Y]

/-- A version of `fundamental_theorem_of_variational_calculus'` for `Continuous f`.
The proof uses assumption that source of `f` is finite-dimensional
inner-product space, so that a bump function with compact support exists via
`ContDiffBump.hasCompactSupport` from `Analysis.Calculus.BumpFunction.Basic`.

The proof is by contradiction, assume that there is `x₀` such that `f x₀ ≠ 0` then one construct
construct `g` test function *supported* on the neighborhood of `x₀` such that `⟪f x, g x⟫ ≥ 0`
and `⟪f x, g x⟫ > 0` on a neighborhood of x₀.

Using `Y` for the theorem below to make use of bump functions in InnerProductSpaces. `Y` is
a finite dimensional measurable space over `ℝ` with (standard) inner product.
-/
lemma fundamental_theorem_of_variational_calculus' {f : Y → V}
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [OpensMeasurableSpace Y]
    (hf : Continuous f) (hg : ∀ g, IsTestFunction g → ∫ x, ⟪f x, g x⟫_ℝ ∂μ = 0) :
    f = 0 := by
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
    have hself : ⟪x₂, x₂⟫_ℝ = ‖x₂‖^2 := real_inner_self_eq_norm_sq (x₂ : WithLp 2 V)
    have hcs : -(‖f₂ x - x₂‖ * ‖x₂‖) ≤ ⟪f₂ x - x₂, x₂⟫_ℝ :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have hxp : 0 < ‖x₂‖ := norm_pos_iff.mpr hx2
    have inner_eq_self_add_diff : ⟪f₂ x, x₂⟫_ℝ = ⟪x₂, x₂⟫_ℝ + ⟪f₂ x - x₂, x₂⟫_ℝ := by
      rw [← inner_add_left]
      simp
    nlinarith [inner_eq_self_add_diff, hcs, hself, hclose, hxp,
      mul_lt_mul_of_pos_right hclose hxp]
  have inner_pos_V : ∀ x ∈ Metric.ball x₀ δ₂, 0 < ⟪f x, f x₀⟫_ℝ := fun x hx => inner_pos₂ x hx
  have bump_exists : ∃ φ : Y → ℝ, IsTestFunction φ ∧ φ x₀ > 0 ∧
      (∀ x ∈ Function.support φ, 0 ≤ φ x) ∧
      Function.support φ ⊆ Metric.ball x₀ (δ₂/2) ∧
      (∀ x ∈ Metric.closedBall x₀ (δ₂/4), 0 < φ x) := by
    haveI : HasContDiffBump Y := hasContDiffBump_of_innerProductSpace Y
    let φ1 : ContDiffBump x₀ :=
      ⟨δ₂ / 4, δ₂ / 2, by positivity, by linarith⟩
    refine ⟨φ1.toFun, ⟨φ1.contDiff, φ1.hasCompactSupport⟩,
      φ1.pos_of_mem_ball (Metric.mem_ball_self φ1.rOut_pos), fun x _ => φ1.nonneg,
      by rw [ContDiffBump.support_eq], fun x hx => φ1.pos_of_mem_ball ?_⟩
    rw [Metric.mem_closedBall] at hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hx (by show δ₂ / 4 < δ₂ / 2; linarith))
  obtain ⟨φ, hφ_testfun, hφ_pos_x₀, hφ_non_neg, hφ_support_subset, hφ_pos_inner⟩ :=
    bump_exists
  let g : Y → V := fun x => φ x • f x₀
  have hg_test : IsTestFunction g := IsTestFunction.smul_right hφ_testfun contDiff_const
  have key_integral := hg g hg_test
  simp only [g, inner_smul_right'] at key_integral
  have support_subset : Function.support φ ⊆ Metric.ball x₀ δ₂ :=
    hφ_support_subset.trans (Metric.ball_subset_ball (by linarith))
  have supp_subset2 : Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) ⊆ Function.support φ := by
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
  have hμ_ball : 0 < μ (Metric.ball x₀ (δ₂/4)) :=
    Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr (by linarith))
  have hμ : 0 < μ (Metric.closedBall x₀ (δ₂/4)) :=
    lt_of_lt_of_le hμ_ball (measure_mono Metric.ball_subset_closedBall)
  have closedBall_subset_support :
      Metric.closedBall x₀ (δ₂/4)
        ⊆ Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) := by
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

/- A version of `fundamental_theorem_of_variational_calculus` for test functions `f`.
Source/domain `X` of `f` is not assumed to be a finite-dimensional space, and
`hf` gives compact support for `f`.
-/

lemma fundamental_theorem_of_variational_calculus {f : X → V}
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [OpensMeasurableSpace X]
    (hf : IsTestFunction f) (hg : ∀ g, IsTestFunction g → ∫ x, ⟪f x, g x⟫_ℝ ∂μ = 0) :
    f = 0 := by
  have hf' := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at hf'
  · rw [Continuous.ae_eq_iff_eq] at hf'
    · funext x
      have hf'' := congrFun hf' x
      simpa using hf''
    · have hf : Continuous f := hf.smooth.continuous
      fun_prop
    · fun_prop
  · intro x
    simp only [Pi.zero_apply]
    apply real_inner_self_nonneg'
  · apply IsTestFunction.integrable
    exact IsTestFunction.inner hf hf
