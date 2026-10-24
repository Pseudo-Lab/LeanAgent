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
  funext x
  by_contra hx
  have hxx : 0 < ⟪f x, f x⟫_ℝ := by
    have hne : ⟪f x, f x⟫_ℝ ≠ 0 := by
      intro h
      apply hx
      simpa using h
    exact lt_of_le_of_ne (real_inner_self_nonneg' _) (Ne.symm hne)
  have hinner_cont : Continuous (fun y => ⟪f y, f x⟫_ℝ) := by
    fun_prop
  have hopen : IsOpen ((fun y => ⟪f y, f x⟫_ℝ) ⁻¹' Set.Ioi 0) :=
    isOpen_Ioi.preimage hinner_cont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hxx
  let φ : ContDiffBump x := ContDiffBump.ofInnerProductSpace x ε hε
  have hφ_cont : Continuous (φ : Y → ℝ) := φ.contDiff.continuous
  have hg_cont : Continuous (fun y => φ y • f x) := by
    fun_prop
  have hg_compact : HasCompactSupport (fun y => φ y • f x) := by
    apply φ.hasCompactSupport.mono
    intro y hy hφy
    apply hy
    simp [hφy]
  have htest : IsTestFunction (fun y => φ y • f x) := by
    constructor
    · exact φ.contDiff.smul contDiff_const
    · exact hg_compact
  have hnonneg : ∀ y, 0 ≤ ⟪f y, φ y • f x⟫_ℝ := by
    intro y
    by_cases hy : φ y = 0
    · simp [hy]
    · have hyball : y ∈ Metric.ball x ε := by
        have hy' : y ∈ Function.support (φ : Y → ℝ) := hy
        rw [φ.support_eq] at hy'
        simpa [φ] using hy'
      rw [real_inner_smul_right]
      exact mul_nonneg (φ.nonneg y) (le_of_lt (hball hyball))
  have hintegrand_cont : Continuous (fun y => ⟪f y, φ y • f x⟫_ℝ) := by
    fun_prop
  have hintegrand_compact : HasCompactSupport (fun y => ⟪f y, φ y • f x⟫_ℝ) := by
    apply hg_compact.mono
    intro y hy hgy
    apply hy
    simp [hgy]
  have hi := hg (fun y => φ y • f x) htest
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at hi
  · rw [Continuous.ae_eq_iff_eq] at hi
    · have hφx : φ x = 1 := by
        apply φ.one_of_mem_closedBall
        simp [φ]
      apply hx
      simpa [hφx] using congrFun hi x
    · exact hintegrand_cont
    · fun_prop
  · exact hnonneg
  · exact hintegrand_cont.integrable_of_hasCompactSupport hintegrand_compact

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
