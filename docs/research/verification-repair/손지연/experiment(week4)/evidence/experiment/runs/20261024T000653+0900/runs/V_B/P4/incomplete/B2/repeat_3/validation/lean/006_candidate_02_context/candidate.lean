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

#repair_context
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
  have hf' := hg f hf
  rw [MeasureTheory.integral_eq_zero_iff_of_nonneg] at hf'
  · rw [Continuous.ae_eq_iff_eq] at hf'
    · funext x
      have hf'' := congrFun hf' x
      simpa using hf''
    · have hfcont : Continuous f := hf.smooth.continuous
      fun_prop
    · fun_prop
  · intro x
    simp only [Pi.zero_apply]
    apply real_inner_self_nonneg'
  · apply IsTestFunction.integrable
    exact IsTestFunction.inner hf hf

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
