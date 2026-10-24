/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.VariationalCalculus.IsTestFunction
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

import Lean

meta section
set_option maxHeartbeats 0

/-!
Small evaluator instrumentation. The Python runner inlines this after the source
imports, preserving the project's parser environment at the target declaration.

`#repair_guard "by\n  ..."` parses exactly one complete `by` term as data, counts
its native Lean lexer tokens, and rejects selected executable/incomplete-proof
syntax before candidate elaboration. Project tactics and notation are allowed.
This denylist is a boundary check for trusted local projects, not a sandbox for
hostile Lean or a proof of semantic preservation. Imported macros/tactics remain
trusted. The runner also fixes the surrounding source and checks actual axioms.

`#repair_measure <command>` measures only the wrapped command's elaboration in
raw allocation heartbeats. Run with `-DElab.async=false`; otherwise theorem work
may occur on another thread. Raw heartbeats are 1000 times maxHeartbeats units.
The runner enforces the limit independently, including source-local options.

`#repair_context <command>` is a diagnostic-only replay. It records native tactic
InfoTree states (including nested/multiline tactics, bullets and case blocks), not
states inferred by editing individual tactic lines. Ranges are UTF-8 byte offsets
in this instrumented file; the Python adapter maps them to the original source.
-/

namespace LeanRepairSupport

open Lean Elab Command

private def blockedWords : Array String := #[
  "sorry", "sorryAx", "admit", "axiom", "unsafe", "implemented_by", "extern",
  "run_tac", "run_elab", "run_meta", "run_io", "by_elab", "elab", "elab_rules",
  "macro", "macro_rules", "initialize", "builtin_initialize", "native_decide",
  "eval", "eval%", "eval_expr", "set_option", "trustCompiler", "ofReduceBool"
]

private def blockedName (name : String) : Bool :=
  (name.splitOn ".").any (fun p => blockedWords.contains p && p != "eval") ||
  name == "IO" || name.startsWith "IO." ||
  name == "System" || name.startsWith "System." ||
  name == "Lean" || name.startsWith "Lean."

private partial def forbidden? : Syntax → Option String
  | .atom _ value =>
      if blockedWords.contains value || (value.startsWith "#" && value != "#") then some value else none
  | .ident _ raw name _ =>
      if blockedName name.toString || blockedName raw.toString then some raw.toString else none
  | .node _ kind args =>
      if kind.toString.startsWith "Lean.Parser.Command." then some kind.toString
      else args.foldl (fun found arg => found.orElse (fun _ => forbidden? arg)) none
  | .missing => none

/-- Count the actual lexer token stream; whitespace and comments are skipped. -/
private def countTokens (env : Environment) (body : String) : Except String Nat := Id.run do
  let input := Parser.mkInputContext body "<repair_body>"
  let moduleCtx : Parser.ParserModuleContext := { env, options := {} }
  let tokens := Parser.getTokenTable env
  let mut state := Parser.whitespace.run input moduleCtx tokens (Parser.mkParserState body)
  let mut count := 0
  while !input.atEnd state.pos do
    let previous := state.pos
    state := (Parser.tokenFn []).run input moduleCtx tokens state
    if state.hasError then return .error (state.toErrorMsg input)
    if state.pos == previous then return .error "Lean lexer made no progress"
    count := count + 1
    state := { state with stxStack := .empty }
  return .ok count

elab "#repair_guard " text:str : command => do
  let body := text.getString
  let env ← getEnv
  let parsed ← match Parser.runParserCategory env `term body "<repair_body>" with
    | .error message => throwError "repair guard: {message}"
    | .ok parsedSyntax => pure parsedSyntax
  unless parsed.getKind == ``Lean.Parser.Term.byTactic do
    throwError "repair guard: proof body must be one complete `by` term"
  if let some blocked := forbidden? parsed then
    throwError "repair guard: forbidden syntax or identifier `{blocked}`"
  let count ← match countTokens env body with
    | .error message => throwError "repair lexer: {message}"
    | .ok count => pure count
  logInfo m!"REPAIR_GUARD|{count}"

elab "#repair_measure " cmd:command : command => do
  let started ← IO.getNumHeartbeats
  try
    elabCommand cmd
  finally
    let finished ← IO.getNumHeartbeats
    logInfo m!"REPAIR_HEARTBEATS|{finished - started}"

private def sourceRange (stx : Syntax) : List (String × Json) :=
  match stx.getPos?, stx.getTailPos? with
  | some first, some last => [("start", toJson first.byteIdx), ("end", toJson last.byteIdx)]
  | _, _ => []

private partial def sorryRanges (stx : Syntax) : Array Json := Id.run do
  match stx with
  | .atom _ value =>
    if value == "sorry" || value == "admit" then
      return #[Json.mkObj (("kind", .str "explicit_sorry") :: sourceRange stx)]
    return #[]
  | .node _ _ args => return args.foldl (fun found arg => found ++ sorryRanges arg) #[]
  | _ => return #[]

private partial def tacticStates (tree : InfoTree) (outer? : Option ContextInfo := none)
    (depth : Nat := 0) : IO (Array Json) := do
  match tree with
  | .context context tree => tacticStates tree (context.mergeIntoOuter? outer?) depth
  | .node info children =>
    let mut result := #[]
    if let .ofTacticInfo tactic := info then
      if let some context := outer? then
        let context := { context with mctx := tactic.mctxBefore }
        let states ← tactic.goalsBefore.toArray.mapM fun goal =>
          context.runMetaM {} do return (← Meta.ppGoal goal).pretty
        let afterContext := { context with mctx := tactic.mctxAfter }
        let after ← tactic.goalsAfter.toArray.mapM fun goal =>
          afterContext.runMetaM {} do return (← Meta.ppGoal goal).pretty
        result := result.push <| Json.mkObj <| sourceRange tactic.stx ++ [
          ("kind", .str "tactic"), ("depth", toJson depth),
          ("goals_before", toJson states), ("goals_after", toJson after)]
    for child in children do
      result := result ++ (← tacticStates child outer? (depth + 1))
    return result
  | .hole _ => return #[]

elab "#repair_context " cmd:command : command => do
  let saved ← getResetInfoTrees
  try
    try
      withEnableInfoTree true <| elabCommand cmd
    finally
      let info ← getInfoState
      let mut records := sorryRanges cmd
      for tree in info.trees do
        let tree := tree.substitute info.assignment
        records := records ++ (← liftIO <| tacticStates tree)
      logInfo m!"REPAIR_CONTEXT|{(Json.arr records).compress}"
  finally
    let current ← getInfoState
    modifyInfoState fun state => { state with trees := saved.append current.trees }

elab "#repair_axioms " target:ident : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos target
  unless names.length == 1 do
    throwError "repair axiom audit: target must resolve to one declaration"
  let name := names[0]!
  let axioms ← collectAxioms name
  let result := Json.mkObj [
    ("target", .str name.toString),
    ("axioms", .arr ((axioms.qsort Name.lt).map (fun n => .str n.toString)))
  ]
  logInfo m!"REPAIR_AXIOMS|{result.compress}"

end LeanRepairSupport

end
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

#repair_guard "by\n  -- assume ¬(f = 0)\n    rw [funext_iff]; by_contra h₀\n    obtain ⟨x₀, hx0⟩ := not_forall.1 h₀\n    simp at hx0 -- hx0 : f x₀ ≠ 0\n\n  -- [1] Proof that `f` is continuous at `x₀`.\n  -- Embed into the true IP-space `WithLp 2 V`.\n    let f₂ : Y → WithLp 2 V := toL2 ℝ ∘ f\n    let x₂ := f₂ x₀\n  -- x₂ ≠ 0 because `fromL2 (toL2 (f x₀)) = f x₀`\n    have hx2 : x₂ ≠ 0 := by\n      intro h; apply hx0; exact congrArg (fromL2 ℝ) h\n  -- continuity of f₂ at x₀\n    have hcont₂ : ContinuousAt f₂ x₀ := ((toL2 ℝ).continuous.comp hf).continuousAt\n\n  -- [2] find open neighborhood guaranteeing positive inner product with the center, based on\n  -- which the test function `g` will be constructed.\n  -- pick δ₂ so that on B(x₀, δ₂), ‖f₂ x - x₂‖ < ‖x₂‖/2\n    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=\n    Metric.continuousAt_iff.mp hcont₂ (‖x₂‖ / 2)\n      (by simpa [half_pos] using (norm_pos_iff.mpr hx2))\n  -- now the usual “add & subtract” proof inside WithLp 2 V\n    have inner_pos₂ : ∀ x (hx : x ∈ Metric.ball x₀ δ₂), 0 < (⟪f₂ x, x₂⟫_ℝ : ℝ) := by\n      intros x hx\n    -- hx : x ∈ ball x₀ δ₂, so dist x x₀ < δ₂, hence\n    -- this is |⟪u,v⟫| ≤ ‖u‖ * ‖v‖, in the genuine InnerProductSpace on WithLp 2 V\n      have hclose : ‖f₂ x - x₂‖ < ‖x₂‖ / 2 := by\n        convert hδ₂ hx using 1\n        exact experiment_missing_lemma\n      have hself : ⟪x₂, x₂⟫_ℝ = ‖x₂‖^2 := real_inner_self_eq_norm_sq (x₂ : WithLp 2 V)\n      -- Cauchy–Schwarz in `WithLp 2 V` bounds the cross term from below\n      have hcs : -(‖f₂ x - x₂‖ * ‖x₂‖) ≤ ⟪f₂ x - x₂, x₂⟫_ℝ :=\n        neg_le_of_abs_le (abs_real_inner_le_norm _ _)\n      have hxp : 0 < ‖x₂‖ := norm_pos_iff.mpr hx2\n      have inner_eq_self_add_diff : ⟪f₂ x, x₂⟫_ℝ = ⟪x₂, x₂⟫_ℝ + ⟪f₂ x - x₂, x₂⟫_ℝ := by\n        rw [← inner_add_left]; simp\n      nlinarith [inner_eq_self_add_diff, hcs, hself, hclose, hxp,\n        mul_lt_mul_of_pos_right hclose hxp]\n  -- pull `inner_pos₂` back to V via `fromL2`:\n    have inner_pos_V : ∀ x ∈ Metric.ball x₀ δ₂, 0 < ⟪f x, f x₀⟫_ℝ := fun x hx => inner_pos₂ x hx\n    -- now we have a genuine positive integrand on a set of positive measure.\n\n  -- [3] `g` construction using bump function.\n    have bump_exists : ∃ φ : Y → ℝ, IsTestFunction φ ∧ φ x₀ > 0 ∧\n        (∀ x ∈ Function.support φ, 0 ≤ φ x) ∧\n        Function.support φ ⊆ Metric.ball x₀ (δ₂/2) ∧\n        (∀ x ∈ Metric.closedBall x₀ (δ₂/4), 0 < φ x) := by\n        -- use `hasContDiffBump_of_innerProductSpace`, leveraging `[innerProductSpace Y]`\n          haveI : HasContDiffBump Y := hasContDiffBump_of_innerProductSpace Y\n          let φ1 : ContDiffBump x₀ :=\n            ⟨δ₂ / 4, δ₂ / 2, by positivity, by linarith⟩\n          refine ⟨φ1.toFun, ⟨φ1.contDiff, φ1.hasCompactSupport⟩,\n            φ1.pos_of_mem_ball (Metric.mem_ball_self φ1.rOut_pos), fun x _ => φ1.nonneg,\n            by rw [ContDiffBump.support_eq], fun x hx => φ1.pos_of_mem_ball ?_⟩\n        -- the closed ball of radius `δ₂/4` lies in the open ball of radius `rOut = δ₂/2`\n          rw [Metric.mem_closedBall] at hx\n          exact Metric.mem_ball.mpr (lt_of_le_of_lt hx (by show δ₂ / 4 < δ₂ / 2; linarith))\n    obtain ⟨φ, hφ_testfun, hφ_pos_x₀, hφ_non_neg, hφ_support_subset, hφ_pos_inner⟩ :=\n      bump_exists\n  -- Define test function g(x) = φ(x) * f(x₀)\n    let g : Y → V := fun x => φ x • f x₀\n  -- Show that g is a test function: `φ` is a test function and `f x₀` is smooth (constant)\n    have hg_test : IsTestFunction g := IsTestFunction.smul_right hφ_testfun contDiff_const\n\n  -- [4] Derive contradiction. First compute the integral ∫ ⟪f x, g x⟫\n  -- [4.1] ∫ φ x * ⟪f x, f x₀⟫ = 0\n    have key_integral := hg g hg_test\n  -- linearity of inner product in the second argument turns the integrand into `φ x * ⟪f x, f x₀⟫`\n    simp only [g, inner_smul_right'] at key_integral\n\n  -- [4.2] 0 < ∫ x, φ x * ⟪f x, f x₀⟫_ℝ ∂μ. Sketch: on the support of φ (which is contained in\n  -- B(x₀, δ/2) ⊆ B(x₀, δ)), we have ⟪f x, f x₀⟫ > ‖f x₀‖²/2 > 0 by our choice of δ.\n  -- Since φ is nonnegative on its support and positive somewhere, this gives the contradiction.\n\n  -- [4.2.1] Integrability of the integrand: `integrable_prod` .\n    have support_subset : Function.support φ ⊆ Metric.ball x₀ δ₂ :=\n      hφ_support_subset.trans (Metric.ball_subset_ball (by linarith))\n    have supp_subset2 : Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) ⊆ Function.support φ := by\n      intro x hprod hφ0\n    -- if φ x = 0 then φ x * inner = 0, contradiction\n      simp [hφ0] at hprod\n    have hinner_cont : Continuous (fun x => ⟪f x, f x₀⟫_ℝ) :=\n      Continuous.inner' (f : Y → V) (fun _ => f x₀) hf continuous_const\n    have integrable_prod :\n      Integrable (fun x => φ x * ⟪f x, f x₀⟫_ℝ) μ :=\n    -- (i) build a `HasCompactSupport` witness for the product\n      (Continuous.mul hφ_testfun.smooth.continuous hinner_cont).integrable_of_hasCompactSupport\n        (hφ_testfun.supp.mono supp_subset2)\n\n  -- [4.2.2] Nonnegativity everywhere (`h_nonneg`)\n    have h_nonneg : ∀ x, 0 ≤ φ x * ⟪f x, f x₀⟫_ℝ := by\n      intro x\n      by_cases hx : x ∈ Function.support φ\n      · -- on the support, φ ≥ 0 and ⟪f x, f x₀⟫ > 0\n        exact mul_nonneg (hφ_non_neg x hx) (inner_pos_V x (support_subset hx)).le\n      · -- off the support, φ x = 0 so the product is 0\n        simp [Function.notMem_support.mp hx]\n\n  -- [4.2.3] That closed ball has positive measure, and is contained in the support\n    -- every nonempty open set has positive measure\n    have hμ_ball : 0 < μ (Metric.ball x₀ (δ₂/4)) :=\n      Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr (by linarith))\n    have hμ : 0 < μ (Metric.closedBall x₀ (δ₂/4)) :=\n      lt_of_lt_of_le hμ_ball (measure_mono Metric.ball_subset_closedBall)\n    have closedBall_subset_support :\n        Metric.closedBall x₀ (δ₂/4)\n          ⊆ Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) := by\n        intro x hx\n        have hφx := hφ_pos_inner x hx\n        have hin : 0 < ⟪f x, f x₀⟫_ℝ :=\n          inner_pos_V x (Metric.closedBall_subset_ball (by linarith) hx)\n        simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq]\n        constructor\n        · linarith\n        · linarith\n\n  -- [4.2.4] putting everything together: positivity contradicts `key_integral : ∫ ... = 0`\n    have integral_pos : 0 < ∫ x, φ x * ⟪f x, f x₀⟫_ℝ ∂μ :=\n      (integral_pos_iff_support_of_nonneg h_nonneg integrable_prod).mpr\n        (lt_of_lt_of_le hμ (measure_mono closedBall_subset_support))\n    linarith"
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
  sorry


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
