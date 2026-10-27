/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Electromagnetism.Dynamics.Lagrangian

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

# Extrema of the Lagrangian density

## i. Overview

In this module we define what it means for an electromagnetic potential
to be an extremum of the Lagrangian density in presence of a Lorentz current density.

This is equivalent to the electromagnetic potential satisfying
Maxwell's equations with sources, i.e. Gauss's law and Ampère's law.

## ii. Key results

- `IsExtrema` : The condition on an electromagnetic potential to be an extrema of the lagrangian.
- `isExtrema_iff_gauss_ampere_magneticFieldMatrix` : The electromagnetic potential is an extrema
  of the lagrangian if and only if Gauss's law and Ampère's law hold
  (in terms of the magnetic field matrix).
- `time_deriv_time_deriv_magneticFieldMatrix_of_isExtrema` : A wave-like equation for the
  magnetic field matrix from the extrema condition.
- `time_deriv_time_deriv_electricField_of_isExtrema` : A wave-like equation for the
  electric field from the extrema condition.

## iii. Table of contents

- A. The condition for an extrema of the Lagrangian density
  - A.1. Extrema condition in terms of the field strength matrix
  - A.2. Extrema condition in terms of tensors
  - A.3. Equivariance of the extrema condition
- B. Gauss's law and Ampère's law and the extrema condition
- C. Time derivatives from the extrema condition
- D. Second time derivatives from the extrema condition
  - D.1. Second time derivatives of the magnetic field from the extrema condition
  - D.2. Second time derivatives of the electric field from the extrema condition

## iv. References

-/

@[expose] public section
namespace Electromagnetism
open Module realLorentzTensor
open TensorSpecies
open Tensor ContDiff

namespace ElectromagneticPotential

open TensorSpecies
open Tensor
open SpaceTime
open TensorProduct
open minkowskiMatrix
open InnerProductSpace
open Lorentz.Vector
open Time Space
attribute [-simp] Fintype.sum_sum_type
attribute [-simp] Nat.succ_eq_add_one

/-!

## A. The condition for an extrema of the Lagrangian density

-/

/-- The condition on an electromagnetic potential to be an extrema of the lagrangian. -/
def IsExtrema {d} (𝓕 : FreeSpace) (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) : Prop :=
  gradLagrangian 𝓕 A J = 0

lemma isExtrema_iff_gradLagrangian {𝓕 : FreeSpace} (A : ElectromagneticPotential d)
    (J : LorentzCurrentDensity d) :
    IsExtrema 𝓕 A J ↔ A.gradLagrangian 𝓕 J = 0 := by rfl

/-!

### A.1. Extrema condition in terms of the field strength matrix

-/

lemma isExtrema_iff_fieldStrengthMatrix {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J) :
    IsExtrema 𝓕 A J ↔
    ∀ x, ∀ ν, ∑ μ, ∂_ μ (A.fieldStrengthMatrix · (μ, ν)) x = 𝓕.μ₀ * J x ν := by
  rw [isExtrema_iff_gradLagrangian, gradLagrangian_eq_sum_fieldStrengthMatrix A hA J hJ, funext_iff]
  conv_lhs =>
    enter [x, 1, 2, ν]
    rw [smul_smul]
  conv_lhs =>
    enter [x]
    simp only [one_div, Pi.zero_apply]
    rw [Lorentz.Vector.sum_basis_eq_zero_iff]
  apply Iff.intro
  · intro h x ν
    specialize h x ν
    simp at h
    have h' : η ν ν ≠ 0 := η_diag_ne_zero
    simp_all
    linear_combination (norm := field_simp) 𝓕.μ₀ * h
    ring
  · intro h x ν
    specialize h x ν
    simp only [mul_eq_zero]
    right
    linear_combination (norm := field_simp) 𝓕.μ₀⁻¹ * h
    ring

/-!

### A.2. Extrema condition in terms of tensors

The electromagnetic potential is an exterma of the lagrangian if and only if

$$\frac{1}{\mu_0} \partial_\mu F^{\mu \nu} - J^{\nu} = 0.$$

-/

attribute [-simp] Nat.reduceAdd Nat.reduceSucc Fin.isValue

lemma isExtrema_iff_tensors {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J) :
    IsExtrema 𝓕 A J ↔ ∀ x,
    {((1/ 𝓕.μ₀ : ℝ) • tensorDeriv A.toFieldStrength x | κ κ ν') + - (J x | ν')}ᵀ = 0 := by
  apply Iff.intro
  · intro h
    simp only [IsExtrema] at h
    intro x
    have h1 : ((Tensorial.toTensor (M := Lorentz.Vector d)).symm
        (permT id (IsReindexing.auto) {((1/ 𝓕.μ₀ : ℝ) • tensorDeriv A.toFieldStrength x | κ κ ν') +
        - (J x | ν')}ᵀ)) = 0 := by
      funext ν
      have h2 : gradLagrangian 𝓕 A J x ν = 0 := by simp [h]
      rw [gradLagrangian_eq_tensor A hA J hJ] at h2
      simp only [one_div, map_smul, map_neg, map_add,
        permT_permT, CompTriple.comp_eq, apply_add, apply_smul, Lorentz.Vector.neg_apply,
        mul_eq_zero] at h2
      have hn : η ν ν ≠ 0 := η_diag_ne_zero
      simp_all only [false_or, ne_eq, one_div, map_smul,
        map_neg, map_add, permT_permT, CompTriple.comp_eq, apply_add, apply_smul,
        Lorentz.Vector.neg_apply, Lorentz.Vector.zero_apply]
    generalize {((1/ 𝓕.μ₀ : ℝ) • tensorDeriv A.toFieldStrength x | κ κ ν') +
        - (J x | ν')}ᵀ = V at *
    simp only [EmbeddingLike.map_eq_zero_iff] at h1
    rw [permT_eq_zero_iff] at h1
    exact h1
  · intro h
    simp only [IsExtrema]
    funext x
    funext ν
    rw [gradLagrangian_eq_tensor A hA J hJ, h]
    simp only [map_zero, Lorentz.Vector.zero_apply, mul_zero, Pi.zero_apply]

/-!

### A.3. Equivariance of the extrema condition

If `A` is an extrema of the lagrangian with current density `J`, then the Lorentz transformation
`Λ • A (Λ⁻¹ • x)` is an extrema of the lagrangian with current density `Λ • J (Λ⁻¹ • x)`.

Combined with `time_deriv_time_deriv_electricField_of_isExtrema`, this shows that
the speed with which an electromagnetic wave propagates is invariant under Lorentz transformations.

-/

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
lemma isExtrema_lorentzGroup_apply_iff {𝓕 : FreeSpace}
    (A : ElectromagneticPotential d)
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J)
    (Λ : LorentzGroup d) :
    IsExtrema 𝓕 (Λ • A) (fun x => Λ • J (Λ⁻¹ • x)) ↔
    IsExtrema 𝓕 A J := by
  rw [isExtrema_iff_tensors]
  conv_lhs =>
    enter [x, 1, 1, 2, 2, 2]
    change tensorDeriv (fun x => toFieldStrength (Λ • A) x) x
    enter [1,x]
    rw [toFieldStrength_equivariant _ _ (hA.differentiable (by simp))]
  conv_lhs =>
    enter [x]
    rw [tensorDeriv_equivariant _ _ _ (differentiable_toFieldStrength_of_smooth hA)]
    rw [smul_comm]
    rw [Tensorial.toTensor_smul, Tensorial.toTensor_smul]
    simp only [one_div, map_smul, actionT_smul,
      contrT_equivariant, map_neg, permT_equivariant]
    rw [smul_comm, ← Tensor.actionT_neg, ← Tensor.actionT_add]
  apply Iff.intro
  · intro h
    rw [isExtrema_iff_tensors A hA J hJ]
    intro x
    apply MulAction.injective Λ
    simp only [one_div, map_smul, map_neg,
      _root_.smul_add, actionT_smul, _root_.smul_neg, _root_.smul_zero]
    simpa using h (Λ • x)
  · intro h x
    rw [isExtrema_iff_tensors A hA J hJ] at h
    specialize h (Λ⁻¹ • x)
    simp at h
    rw [h]
    simp
  · change ContDiff ℝ ∞ (actionCLM Λ ∘ A ∘ actionCLM Λ⁻¹)
    apply ContDiff.comp
    · exact ContinuousLinearMap.contDiff (actionCLM Λ)
    · apply ContDiff.comp
      · exact hA
      · exact ContinuousLinearMap.contDiff (actionCLM Λ⁻¹)
  · change ContDiff ℝ ∞ (actionCLM Λ ∘ J ∘ actionCLM Λ⁻¹)
    apply ContDiff.comp
    · exact ContinuousLinearMap.contDiff (actionCLM Λ)
    · apply ContDiff.comp
      · exact hJ
      · exact ContinuousLinearMap.contDiff (actionCLM Λ⁻¹)

/-!

## B. Gauss's law and Ampère's law and the extrema condition

-/

lemma isExtrema_iff_gauss_ampere_magneticFieldMatrix {d} {𝓕 : FreeSpace}
    {A : ElectromagneticPotential d}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) :
    IsExtrema 𝓕 A J ↔ ∀ t, ∀ x, (∇ ⬝ (A.electricField 𝓕.c t)) x = J.chargeDensity 𝓕.c t x / 𝓕.ε₀
    ∧ ∀ i, 𝓕.μ₀ * 𝓕.ε₀ * ∂ₜ (fun t => A.electricField 𝓕.c t x) t i =
    ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c t · (j, i)) x - 𝓕.μ₀ * J.currentDensity 𝓕.c t x i := by
  rw [isExtrema_iff_gradLagrangian]
  rw [funext_iff]
  conv_lhs =>
    enter [x]
    rw [gradLagrangian_eq_electricField_magneticField (𝓕 := 𝓕) A hA J hJ]
    simp only [Pi.zero_apply]
    rw [Lorentz.Vector.sum_inl_inr_basis_eq_zero_iff]
  simp only [forall_and]
  apply and_congr
  · apply Iff.intro
    · intro h t x
      specialize h ((toTimeAndSpace 𝓕.c).symm (t, x))
      simp at h
      linear_combination (norm := simp) (𝓕.μ₀ * 𝓕.c) * h
      field_simp
      simp only [FreeSpace.c_sq, one_div, mul_inv_rev, mul_zero]
      field_simp
      ring
    · intro h x
      specialize h (x.time 𝓕.c) x.space
      linear_combination (norm := simp) (𝓕.μ₀⁻¹ * 𝓕.c⁻¹) * h
      field_simp
      simp only [FreeSpace.c_sq, one_div, mul_inv_rev, mul_zero]
      field_simp
      ring
  · apply Iff.intro
    · intro h t x i
      specialize h ((toTimeAndSpace 𝓕.c).symm (t, x)) i
      simp at h
      linear_combination (norm := simp) (𝓕.μ₀) * h
      field_simp
      simp
    · intro h x i
      specialize h (x.time 𝓕.c) x.space i
      linear_combination (norm := simp) (𝓕.μ₀⁻¹) * h
      field_simp
      simp

/-!

## C. Time derivatives from the extrema condition

-/

lemma time_deriv_electricField_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d) (hJ : ContDiff ℝ ∞ J)
    (h : IsExtrema 𝓕 A J) (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (A.electricField 𝓕.c · x) t i =
      1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c t · (j, i)) x -
      (1/ 𝓕.ε₀) * J.currentDensity 𝓕.c t x i := by
  rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ] at h
  linear_combination (norm := simp) (𝓕.μ₀ * 𝓕.ε₀)⁻¹ * ((h t x).2 i)
  field_simp
  ring

/-!

## D. Second time derivatives from the extrema condition

-/

/-!

### D.1. Second time derivatives of the magnetic field from the extrema condition

We show that the magnetic field matrix $B_{ij}$ satisfies the following wave-like equation

$$\frac{\partial^2 B_{ij}}{\partial t^2} = c^2 \sum_k \frac{\partial^2 B_{ij}}{\partial x_k^2} +
  \frac{1}{\epsilon_0} \left(\frac{\partial J_i}{\partial x_j} -
  \frac{\partial J_j}{\partial x_i} \right).$$
When the free current density is zero, this reduces to the wave equation.
-/

lemma time_deriv_time_deriv_magneticFieldMatrix_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema 𝓕 A J)
    (t : Time) (x : Space d) (i j : Fin d) :
    ∂ₜ (∂ₜ (A.magneticFieldMatrix 𝓕.c · x (i, j))) t =
    𝓕.c ^ 2 * ∑ k, ∂[k] (∂[k] (A.magneticFieldMatrix 𝓕.c t · (i, j))) x +
    𝓕.ε₀⁻¹ * (∂[j] (J.currentDensity 𝓕.c t · i) x - ∂[i] (J.currentDensity 𝓕.c t · j) x) := by
  have hcd : ∀ ij, ContDiff ℝ 2 (fun y => A.magneticFieldMatrix 𝓕.c t y ij) :=
    fun ij => magneticFieldMatrix_space_contDiff _ (hA.of_le (right_eq_inf.mp rfl)) t ij
  have hsd : ∀ ij k, Differentiable ℝ (∂[k] (fun y => A.magneticFieldMatrix 𝓕.c t y ij)) :=
    fun ij k => Space.deriv_differentiable (hcd ij) k
  have hJd : ∀ i, Differentiable ℝ (fun x => J.currentDensity 𝓕.c t x i) :=
    fun i => LorentzCurrentDensity.currentDensity_apply_differentiable_space
      (hJ.differentiable (by simp)) t i
  rw [time_deriv_time_deriv_magneticFieldMatrix A (hA.of_le (ENat.LEInfty.out))]
  conv_lhs =>
    enter [2, 2, x]
    rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  conv_lhs =>
    enter [1, 2, x]
    rw [time_deriv_electricField_of_isExtrema hA J hJ h]
  rw [Space.deriv_eq_fderiv_basis]
  rw [fderiv_fun_sub ((Differentiable.fun_sum fun i _ => hsd _ i).const_mul _).differentiableAt
      ((hJd _).const_mul _).differentiableAt,
    fderiv_const_mul (Differentiable.fun_sum fun i _ => hsd _ i).differentiableAt,
    fderiv_const_mul (hJd _).differentiableAt,
    fderiv_fun_sum fun i _ => (hsd _ i).differentiableAt]
  conv_lhs =>
    enter [2]
    rw [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub ((Differentiable.fun_sum fun i _ => hsd _ i).const_mul _).differentiableAt
        ((hJd _).const_mul _).differentiableAt,
    fderiv_const_mul (Differentiable.fun_sum fun i _ => hsd _ i).differentiableAt,
    fderiv_const_mul (hJd _).differentiableAt,
    fderiv_fun_sum fun i _ => (hsd _ i).differentiableAt]
  simp [← Space.deriv_eq_fderiv_basis, FreeSpace.c_sq]
  field_simp
  conv_rhs =>
    enter [1, 2, k, 2, x]
    rw [magneticFieldMatrix_space_deriv_eq A (hA.of_le (right_eq_inf.mp rfl))]
  conv_rhs =>
    enter [1, 2, k]
    rw [Space.deriv_eq_fderiv_basis]
    rw [fderiv_fun_sub (hsd _ _).differentiableAt (hsd _ _).differentiableAt]
    simp [← Space.deriv_eq_fderiv_basis]
    rw [Space.deriv_commute _ (hcd _)]
    enter [2]
    rw [Space.deriv_commute _ (hcd _)]
  simp only [Finset.sum_sub_distrib]
  ring

/-!

### D.2. Second time derivatives of the electric field from the extrema condition

We show that the electric field $E_i$ satisfies the following wave-like equation:

$$\frac{\partial^2 E_{i}}{\partial t^2} = c^2 \sum_k \frac{\partial^2 E_{i}}{\partial x_k^2} -
  \frac{c ^ 2}{\epsilon_0} \frac{\partial \rho}{\partial x_i} -
  c ^ 2 μ_0 \frac{\partial J_i}{\partial t}.$$

When the free current density and charge density are zero, this reduces to the wave equation.

-/

#repair_context
lemma time_deriv_time_deriv_electricField_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema 𝓕 A J)
    (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (∂ₜ (A.electricField 𝓕.c · x i)) t =
      𝓕.c ^ 2 * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
      𝓕.c ^ 2 / 𝓕.ε₀ * ∂[i] (J.chargeDensity 𝓕.c t ·) x -
      𝓕.c ^ 2 * 𝓕.μ₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
  have hmax :=
    (isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ).mp h
  have hamp :
      (fun s => ∂ₜ (A.electricField 𝓕.c · x i) s) =
        fun s =>
          1 / (𝓕.μ₀ * 𝓕.ε₀) *
              ∑ j, ∂[j] (A.magneticFieldMatrix 𝓕.c s · (j, i)) x -
            (1 / 𝓕.ε₀) * J.currentDensity 𝓕.c s x i := by
    funext s
    simpa (disch := fun_prop) [Time.deriv] using
      time_deriv_electricField_of_isExtrema hA J hJ h s x i
  have hamp' := congrArg (fun f : Time → ℝ => ∂ₜ f t) hamp
  have hgauss :
      (fun y => ∑ j, ∂[j] (A.electricField 𝓕.c t · j) y) =
        fun y => J.chargeDensity 𝓕.c t y / 𝓕.ε₀ := by
    funext y
    simpa [Space.div] using (hmax t y).1
  have hgauss' := congrArg (fun f : Space d → ℝ => ∂[i] f x) hgauss
  simp (disch := fun_prop)
      [Time.deriv, Space.deriv_eq_fderiv_basis,
        fderiv_fun_sub, fderiv_const_mul, fderiv_fun_sum,
        time_deriv_space_deriv_commute,
        time_deriv_magneticFieldMatrix A (hA.of_le (ENat.LEInfty.out)),
        Space.deriv_commute, Finset.sum_sub_distrib] at hamp' hgauss'
  linear_combination (norm := field_simp [FreeSpace.c_sq]) hamp' -
    (𝓕.c ^ 2) * hgauss'

end ElectromagneticPotential

end Electromagnetism
