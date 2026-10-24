/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.QFT.PerturbationTheory.WickAlgebra.SuperCommute
public import Physlib.QFT.PerturbationTheory.FieldOpFreeAlgebra.TimeOrder

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

# Time Ordering on Field operator algebra

-/

@[expose] public section

namespace FieldSpecification
open Module FieldOpFreeAlgebra
open Physlib.List
open FieldStatistic

namespace WickAlgebra
variable {𝓕 : FieldSpecification}

lemma ι_timeOrderF_superCommuteF_superCommuteF_eq_time_ofCrAnListF {φ1 φ2 φ3 : 𝓕.CrAnFieldOp}
    (φs1 φs2 : List 𝓕.CrAnFieldOp) (h :
      crAnTimeOrderRel φ1 φ2 ∧ crAnTimeOrderRel φ1 φ3 ∧
      crAnTimeOrderRel φ2 φ1 ∧ crAnTimeOrderRel φ2 φ3 ∧
      crAnTimeOrderRel φ3 φ1 ∧ crAnTimeOrderRel φ3 φ2) :
    ι 𝓣ᶠ(ofCrAnListF φs1 * [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛF]ₛF *
    ofCrAnListF φs2) = 0 := by
  calc _
      _ = ι (𝓣ᶠ(ofCrAnListF (φs1 ++ φ1 :: φ2 :: φ3 :: φs2))) -
          𝓢(𝓕.crAnStatistics φ1, (ofList 𝓕.crAnStatistics [φ2, φ3])) •
          ι (𝓣ᶠ(ofCrAnListF (φs1 ++ φ2 :: φ3 :: φ1 :: φs2))) -
          𝓢(𝓕.crAnStatistics φ2, 𝓕.crAnStatistics φ3) •
          (ι (𝓣ᶠ(ofCrAnListF (φs1 ++ φ1 :: φ3 :: φ2 :: φs2))) -
          𝓢(𝓕.crAnStatistics φ1, ofList 𝓕.crAnStatistics [φ3, φ2]) •
          ι 𝓣ᶠ(ofCrAnListF (φs1 ++ φ3 :: φ2 :: φ1 :: φs2))) := by
        rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_singleton]
        rw [superCommuteF_ofCrAnListF_ofCrAnListF]
        simp only [List.singleton_append, ofList_singleton, map_sub, map_smul]
        rw [superCommuteF_ofCrAnListF_ofCrAnListF, superCommuteF_ofCrAnListF_ofCrAnListF]
        simp only [List.cons_append, List.nil_append, ofList_singleton, mul_sub, ←
          ofCrAnListF_append, Algebra.mul_smul_comm, sub_mul, List.append_assoc,
          Algebra.smul_mul_assoc, map_sub, map_smul]
  let l1 :=
    (List.takeWhile (fun c => ¬ crAnTimeOrderRel φ1 c)
    ((φs1 ++ φs2).insertionSort crAnTimeOrderRel))
    ++ (List.filter (fun c => crAnTimeOrderRel φ1 c ∧ crAnTimeOrderRel c φ1) φs1)
  let l2 := (List.filter (fun c => crAnTimeOrderRel φ1 c ∧ crAnTimeOrderRel c φ1) φs2)
    ++ (List.filter (fun c => crAnTimeOrderRel φ1 c ∧ ¬ crAnTimeOrderRel c φ1)
    ((φs1 ++ φs2).insertionSort crAnTimeOrderRel))
  have h123 : ι 𝓣ᶠ(ofCrAnListF (φs1 ++ φ1 :: φ2 :: φ3 :: φs2)) =
      crAnTimeOrderSign (φs1 ++ φ1 :: φ2 :: φ3 :: φs2)
      • (ι (ofCrAnListF l1) * ι (ofCrAnListF [φ1, φ2, φ3]) * ι (ofCrAnListF l2)) := by
    have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ1 φs1 [φ1, φ2, φ3] φs2
      (by simp_all)
    rw [timeOrderF_ofCrAnListF, show φs1 ++ φ1 :: φ2 :: φ3 :: φs2 = φs1 ++ [φ1, φ2, φ3] ++ φs2
      by simp, crAnTimeOrderList, h1]
    simp only [List.append_assoc, decide_not,
      Bool.decide_and, ofCrAnListF_append, map_smul, map_mul, l1, l2, mul_assoc]
  have h132 : ι 𝓣ᶠ(ofCrAnListF (φs1 ++ φ1 :: φ3 :: φ2 :: φs2)) =
      crAnTimeOrderSign (φs1 ++ φ1 :: φ2 :: φ3 :: φs2)
      • (ι (ofCrAnListF l1) * ι (ofCrAnListF [φ1, φ3, φ2]) * ι (ofCrAnListF l2)) := by
    have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ1 φs1 [φ1, φ3, φ2] φs2
        (by simp_all)
    rw [timeOrderF_ofCrAnListF, show φs1 ++ φ1 :: φ3 :: φ2 :: φs2 = φs1 ++ [φ1, φ3, φ2] ++ φs2
      by simp, crAnTimeOrderList, h1]
    simp only [decide_not,
      Bool.decide_and, ofCrAnListF_append, map_smul, map_mul, l1, l2, mul_assoc]
    congr 1
    have hp : List.Perm [φ1, φ3, φ2] [φ1, φ2, φ3] := .cons φ1 (.swap φ2 φ3 [])
    rw [crAnTimeOrderSign, Wick.koszulSign_perm_eq _ _ φ1 _ _ _ _ _ hp, ← crAnTimeOrderSign]
    · simp
    · simp_all
  have hp231 : List.Perm [φ2, φ3, φ1] [φ1, φ2, φ3] :=
    ((List.Perm.swap φ1 φ3 []).cons φ2).trans (List.Perm.swap φ1 φ2 [φ3])
  have h231 : ι 𝓣ᶠ(ofCrAnListF (φs1 ++ φ2 :: φ3 :: φ1 :: φs2)) =
      crAnTimeOrderSign (φs1 ++ φ1 :: φ2 :: φ3 :: φs2)
      • (ι (ofCrAnListF l1) * ι (ofCrAnListF [φ2, φ3, φ1]) * ι (ofCrAnListF l2)) := by
    have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ1 φs1 [φ2, φ3, φ1] φs2
        (by simp_all)
    rw [timeOrderF_ofCrAnListF, show φs1 ++ φ2 :: φ3 :: φ1 :: φs2 = φs1 ++ [φ2, φ3, φ1] ++ φs2
      by simp, crAnTimeOrderList, h1]
    simp only [decide_not,
      Bool.decide_and, ofCrAnListF_append, map_smul, map_mul, l1, l2, mul_assoc]
    congr 1
    rw [crAnTimeOrderSign, Wick.koszulSign_perm_eq _ _ φ1 _ _ _ _ _ hp231, ← crAnTimeOrderSign]
    · simp
    · simp_all
  have h321 : ι 𝓣ᶠ(ofCrAnListF (φs1 ++ φ3 :: φ2 :: φ1 :: φs2)) =
      crAnTimeOrderSign (φs1 ++ φ1 :: φ2 :: φ3 :: φs2)
      • (ι (ofCrAnListF l1) * ι (ofCrAnListF [φ3, φ2, φ1]) * ι (ofCrAnListF l2)) := by
    have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ1 φs1 [φ3, φ2, φ1] φs2
        (by simp_all)
    rw [timeOrderF_ofCrAnListF, show φs1 ++ φ3 :: φ2 :: φ1 :: φs2 = φs1 ++ [φ3, φ2, φ1] ++ φs2
      by simp, crAnTimeOrderList, h1]
    simp only [decide_not,
      Bool.decide_and, ofCrAnListF_append, map_smul, map_mul, l1, l2, mul_assoc]
    congr 1
    have hp : List.Perm [φ3, φ2, φ1] [φ1, φ2, φ3] := (List.Perm.swap φ2 φ3 [φ1]).trans hp231
    rw [crAnTimeOrderSign, Wick.koszulSign_perm_eq _ _ φ1 _ _ _ _ _ hp, ← crAnTimeOrderSign]
    · simp
    · simp_all
  rw [h123, h132, h231, h321]
  trans crAnTimeOrderSign (φs1 ++ φ1 :: φ2 :: φ3 :: φs2) • (ι (ofCrAnListF l1) *
    ι [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛF]ₛF *
    ι (ofCrAnListF l2)); swap
  · simp
  rw [mul_assoc, ← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_singleton,
    superCommuteF_ofCrAnListF_ofCrAnListF]
  simp only [List.singleton_append, ofList_singleton, map_sub, map_smul]
  rw [superCommuteF_ofCrAnListF_ofCrAnListF, superCommuteF_ofCrAnListF_ofCrAnListF]
  simp [List.cons_append, List.nil_append, ofList_singleton, map_sub,
    map_smul, mul_sub, sub_mul, Semigroup.mul_assoc]
  module

lemma ι_timeOrderF_superCommuteF_superCommuteF_ofCrAnListF {φ1 φ2 φ3 : 𝓕.CrAnFieldOp}
    (φs1 φs2 : List 𝓕.CrAnFieldOp) :
    ι 𝓣ᶠ(ofCrAnListF φs1 * [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛF]ₛF * ofCrAnListF φs2)
    = 0 := by
  by_cases h :
      crAnTimeOrderRel φ1 φ2 ∧ crAnTimeOrderRel φ1 φ3 ∧
      crAnTimeOrderRel φ2 φ1 ∧ crAnTimeOrderRel φ2 φ3 ∧
      crAnTimeOrderRel φ3 φ1 ∧ crAnTimeOrderRel φ3 φ2
  · exact ι_timeOrderF_superCommuteF_superCommuteF_eq_time_ofCrAnListF φs1 φs2 h
  · rw [timeOrderF_timeOrderF_mid]
    simp [timeOrderF_superCommuteF_ofCrAnOpF_superCommuteF_all_not_crAnTimeOrderRel _ _ _ h]

@[simp]
lemma ι_timeOrderF_superCommuteF_superCommuteF {φ1 φ2 φ3 : 𝓕.CrAnFieldOp}
    (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓣ᶠ(a * [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛF]ₛF * b) = 0 := by
  let pb (b : 𝓕.FieldOpFreeAlgebra) (hc : b ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
    Prop := ι 𝓣ᶠ(a * [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛF]ₛF * b) = 0
  change pb b (Basis.mem_span _ b)
  apply Submodule.span_induction
  · rintro x ⟨φs, rfl⟩
    simp only [ofListBasis_eq_ofList, pb]
    let pa (a : 𝓕.FieldOpFreeAlgebra) (hc : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
      Prop := ι 𝓣ᶠ(a * [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛF]ₛF * ofCrAnListF φs) = 0
    change pa a (Basis.mem_span _ a)
    apply Submodule.span_induction
    · rintro x ⟨φs', rfl⟩
      simpa only [ofListBasis_eq_ofList, pa] using
        ι_timeOrderF_superCommuteF_superCommuteF_ofCrAnListF φs' φs
    · simp [pa]
    · intro x y hx hy hpx hpy
      simp_all [pa, add_mul]
    · intro x hx hpx
      simp_all [pa]
  · simp [pb]
  · intro x y hx hy hpx hpy
    simp_all [pb,mul_add]
  · intro x hx hpx
    simp_all [pb]

example (c1 c2 : ℂ) (a : 𝓕.WickAlgebra) : c1 • c2 • a =
  c2 • c1 • a := smul_comm c1 c2 a
#repair_guard "by\n  let pb (b : 𝓕.FieldOpFreeAlgebra)\n      (_ : b ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) : Prop :=\n    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * b) =\n      ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * b))\n  change pb b (Basis.mem_span _ b)\n  apply Submodule.span_induction\n  · rintro x ⟨φs, rfl⟩\n    simp only [ofListBasis_eq_ofList, map_mul, pb]\n    let pa (a : 𝓕.FieldOpFreeAlgebra)\n        (_ : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) : Prop :=\n      ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * ofCrAnListF φs) =\n        ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * ofCrAnListF φs))\n    change pa a (Basis.mem_span _ a)\n    apply Submodule.span_induction\n    · rintro x ⟨φs', rfl⟩\n      simp only [ofListBasis_eq_ofList, map_mul, pa]\n      let l1 := List.takeWhile (fun c => ¬crAnTimeOrderRel φ c)\n        (List.insertionSort crAnTimeOrderRel (φs' ++ φs))\n      let l2 := List.filter\n        (fun c => crAnTimeOrderRel φ c ∧ crAnTimeOrderRel c φ) φs'\n      let l3 := List.filter\n        (fun c => crAnTimeOrderRel φ c ∧ crAnTimeOrderRel c φ) φs\n      let l4 := List.filter\n        (fun c => crAnTimeOrderRel φ c ∧ ¬crAnTimeOrderRel c φ)\n        (List.insertionSort crAnTimeOrderRel (φs' ++ φs))\n      calc _\n        _ = crAnTimeOrderSign (φs' ++ φ :: ψ :: φs) •\n              ι (ofCrAnListF (crAnTimeOrderList (φs' ++ φ :: ψ :: φs))) -\n            crAnTimeOrderSign (φs' ++ ψ :: φ :: φs) •\n              𝓢(𝓕.crAnStatistics φ, 𝓕.crAnStatistics ψ) •\n              ι (ofCrAnListF (crAnTimeOrderList (φs' ++ ψ :: φ :: φs))) := by\n          conv_lhs =>\n            rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton,\n              superCommuteF_ofCrAnListF_ofCrAnListF]\n            simp [mul_sub, sub_mul, ← ofCrAnListF_append]\n            rw [timeOrderF_ofCrAnListF, timeOrderF_ofCrAnListF]\n          simp only [map_smul, sub_right_inj]\n          module\n        _ = crAnTimeOrderSign (φs' ++ φ :: ψ :: φs) •\n            (ι (ofCrAnListF (crAnTimeOrderList (φs' ++ φ :: ψ :: φs))) -\n              𝓢(𝓕.crAnStatistics φ, 𝓕.crAnStatistics ψ) •\n              ι (ofCrAnListF (crAnTimeOrderList (φs' ++ ψ :: φ :: φs)))) := by\n          rw [crAnTimeOrderSign_swap_eq_time hφψ hψφ]\n          module\n        _ = crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs) •\n            (ι (ofCrAnListF l1) * ι (ofCrAnListF l2) *\n                ι (ofCrAnListF [φ, ψ]) * ι (ofCrAnListF l3) * ι (ofCrAnListF l4) -\n              𝓢(𝓕.crAnStatistics φ, 𝓕.crAnStatistics ψ) •\n                ι (ofCrAnListF l1) * ι (ofCrAnListF l2) *\n                ι (ofCrAnListF [ψ, φ]) * ι (ofCrAnListF l3) * ι (ofCrAnListF l4)) := by\n          have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ φs' [φ, ψ] φs\n            (by simp_all)\n          rw [crAnTimeOrderList,\n            show φs' ++ φ :: ψ :: φs = φs' ++ [φ, ψ] ++ φs by simp, h1]\n          have h2 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ φs' [ψ, φ] φs\n            (by simp_all)\n          rw [crAnTimeOrderList,\n            show φs' ++ ψ :: φ :: φs = φs' ++ [ψ, φ] ++ φs by simp, h2]\n          repeat rw [ofCrAnListF_append]\n          simp [l1, l2, l3, l4]\n        _ = crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs) •\n            (ι (ofCrAnListF l1) * ι (ofCrAnListF l2) *\n              (ι (ofCrAnListF [φ, ψ]) -\n                𝓢(𝓕.crAnStatistics φ, 𝓕.crAnStatistics ψ) •\n                  ι (ofCrAnListF [ψ, φ])) *\n              ι (ofCrAnListF l3) * ι (ofCrAnListF l4)) := by\n          simp [mul_sub, sub_mul]\n        _ = crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs) •\n            (ι (ofCrAnListF l1) * ι (ofCrAnListF l2) *\n              ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF *\n              ι (ofCrAnListF l3) * ι (ofCrAnListF l4)) := by\n          congr\n          rw [superCommuteF_ofCrAnOpF_ofCrAnOpF, ← ofCrAnListF_singleton,\n            ← ofCrAnListF_singleton]\n          simp [← ofCrAnListF_append]\n      rw [Subalgebra.mem_center_iff.mp\n        (ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_mem_center φ ψ)]\n      repeat rw [mul_assoc]\n      rw [← map_mul, ← map_mul, ← map_mul, ← ofCrAnListF_append,\n        ← ofCrAnListF_append, ← ofCrAnListF_append]\n      have h1 := insertionSort_of_takeWhile_filter 𝓕.crAnTimeOrderRel φ φs' φs\n      simp [l1, l2, l3, l4, decide_not, Bool.decide_and, List.append_assoc,\n        List.cons_append] at h1 ⊢\n      rw [← h1, ← crAnTimeOrderList]\n      by_cases hq : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)\n      · simp [ι_superCommuteF_of_diff_statistic hq]\n      · rw [crAnTimeOrderSign,\n          Wick.koszulSign_eq_rel_eq_stat _ _ hφψ hψφ (by simp_all),\n          ← crAnTimeOrderSign, ← ofCrAnListF_append, timeOrderF_ofCrAnListF]\n        simp only [map_smul, Algebra.mul_smul_comm]\n    · simp only [map_mul, zero_mul, map_zero, mul_zero, pa]\n    · intro x y hx hy hpx hpy\n      simp_all [pa, mul_add, add_mul]\n    · intro x hx hpx\n      simp_all [pa]\n  · simp only [map_mul, mul_zero, map_zero, pb]\n  · intro x y hx hy hpx hpy\n    simp_all [pb, mul_add]\n  · intro x hx hpx\n    simp_all [pb]"
lemma ι_timeOrderF_superCommuteF_eq_time {φ ψ : 𝓕.CrAnFieldOp}
    (hφψ : crAnTimeOrderRel φ ψ) (hψφ : crAnTimeOrderRel ψ φ) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * b) =
    ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * b)) := by
  sorry


lemma ι_timeOrderF_superCommuteF_ne_time {φ ψ : 𝓕.CrAnFieldOp}
    (hφψ : ¬ (crAnTimeOrderRel φ ψ ∧ crAnTimeOrderRel ψ φ)) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * b) = 0 := by
  rw [timeOrderF_timeOrderF_mid]
  rcases Decidable.not_and_iff_or_not.mp hφψ with hφψ | hφψ
  · simp [timeOrderF_superCommuteF_ofCrAnOpF_ofCrAnOpF_not_crAnTimeOrderRel hφψ]
  · rw [superCommuteF_ofCrAnOpF_ofCrAnOpF_symm]
    simp [timeOrderF_superCommuteF_ofCrAnOpF_ofCrAnOpF_not_crAnTimeOrderRel hφψ]

/-!

## Defining time order for `FiedOpAlgebra`.

-/

lemma ι_timeOrderF_zero_of_mem_ideal (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) : ι 𝓣ᶠ(a) = 0 := by
  rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at h
  let p {k : Set 𝓕.FieldOpFreeAlgebra} (a : FieldOpFreeAlgebra 𝓕)
    (h : a ∈ AddSubgroup.closure k) := ι 𝓣ᶠ(a) = 0
  change p a h
  apply AddSubgroup.closure_induction
  · rintro x ⟨_, ⟨a, ha, c, hc, rfl⟩, b, hb, rfl⟩
    simp only [p]
    simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq] at hc
    rcases hc with ⟨φa, φa', hφa, hφa', rfl⟩ | ⟨φa, hφa, φb, hφb, rfl⟩ |
      ⟨φa, hφa, φb, hφb, rfl⟩ | ⟨φa, φb, hdiff, rfl⟩
    · simp
    · by_cases heqt : crAnTimeOrderRel φa φb ∧ crAnTimeOrderRel φb φa
      · rw [ι_timeOrderF_superCommuteF_eq_time heqt.1 heqt.2, map_mul,
          ι_superCommuteF_of_create_create _ _ hφa hφb, zero_mul]
      · rw [ι_timeOrderF_superCommuteF_ne_time heqt]
    · by_cases heqt : crAnTimeOrderRel φa φb ∧ crAnTimeOrderRel φb φa
      · rw [ι_timeOrderF_superCommuteF_eq_time heqt.1 heqt.2, map_mul,
          ι_superCommuteF_of_annihilate_annihilate _ _ hφa hφb, zero_mul]
      · rw [ι_timeOrderF_superCommuteF_ne_time heqt]
    · by_cases heqt : crAnTimeOrderRel φa φb ∧ crAnTimeOrderRel φb φa
      · rw [ι_timeOrderF_superCommuteF_eq_time heqt.1 heqt.2, map_mul,
          ι_superCommuteF_of_diff_statistic hdiff, zero_mul]
      · rw [ι_timeOrderF_superCommuteF_ne_time heqt]
  · simp [p]
  · intro x y hx hy h1 h2
    simp_all [p]
  · intro x hx
    simp [p]

lemma ι_timeOrderF_eq_of_equiv (a b : 𝓕.FieldOpFreeAlgebra) (h : a ≈ b) :
    ι 𝓣ᶠ(a) = ι 𝓣ᶠ(b) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  exact ι_timeOrderF_zero_of_mem_ideal _ ((equiv_iff_sub_mem_ideal a b).mp h)

/-- For a field specification `𝓕`, `timeOrder` is the linear map

`WickAlgebra 𝓕 →ₗ[ℂ] WickAlgebra 𝓕`

defined as the descent of `ι ∘ₗ timeOrderF : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] WickAlgebra 𝓕` from
`FieldOpFreeAlgebra 𝓕` to `WickAlgebra 𝓕`.
This descent exists because `ι ∘ₗ timeOrderF` is well-defined on equivalence classes.

The notation `𝓣(a)` is used for `timeOrder a`. -/
noncomputable def timeOrder : WickAlgebra 𝓕 →ₗ[ℂ] WickAlgebra 𝓕 where
  toFun := Quotient.lift (ι.toLinearMap ∘ₗ timeOrderF) ι_timeOrderF_eq_of_equiv
  map_add' x y := by
    obtain ⟨x, hx⟩ := ι_surjective x
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hx hy
    rw [← map_add, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp
  map_smul' c y := by
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hy
    rw [← map_smul, ι_apply, ι_apply]
    simp

@[inherit_doc timeOrder]
scoped[FieldSpecification.WickAlgebra] notation "𝓣(" a ")" => timeOrder a

/-!

## Properties of time ordering

-/

lemma timeOrder_eq_ι_timeOrderF (a : 𝓕.FieldOpFreeAlgebra) :
    𝓣(ι a) = ι 𝓣ᶠ(a) := rfl

lemma timeOrder_ofFieldOp_ofFieldOp_ordered {φ ψ : 𝓕.FieldOp} (h : timeOrderRel φ ψ) :
    𝓣(ofFieldOp φ * ofFieldOp ψ) = ofFieldOp φ * ofFieldOp ψ := by
  rw [ofFieldOp, ofFieldOp, ← map_mul, timeOrder_eq_ι_timeOrderF,
    timeOrderF_ofFieldOpF_ofFieldOpF_ordered h]

lemma timeOrder_ofFieldOp_ofFieldOp_not_ordered {φ ψ : 𝓕.FieldOp} (h : ¬ timeOrderRel φ ψ) :
    𝓣(ofFieldOp φ * ofFieldOp ψ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • ofFieldOp ψ * ofFieldOp φ := by
  rw [ofFieldOp, ofFieldOp, ← map_mul, timeOrder_eq_ι_timeOrderF,
    timeOrderF_ofFieldOpF_ofFieldOpF_not_ordered h]
  simp

lemma timeOrder_ofFieldOp_ofFieldOp_not_ordered_eq_timeOrder {φ ψ : 𝓕.FieldOp}
    (h : ¬ timeOrderRel φ ψ) :
    𝓣(ofFieldOp φ * ofFieldOp ψ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • 𝓣(ofFieldOp ψ * ofFieldOp φ) := by
  rw [ofFieldOp, ofFieldOp, ← map_mul, timeOrder_eq_ι_timeOrderF,
    timeOrderF_ofFieldOpF_ofFieldOpF_not_ordered_eq_timeOrderF h, map_smul]
  rfl

lemma timeOrder_ofFieldOpList_nil : 𝓣(ofFieldOpList (𝓕 := 𝓕) []) = 1 := by
  rw [ofFieldOpList, timeOrder_eq_ι_timeOrderF, timeOrderF_ofFieldOpListF_nil, map_one]

@[simp]
lemma timeOrder_ofFieldOpList_singleton (φ : 𝓕.FieldOp) :
    𝓣(ofFieldOpList [φ]) = ofFieldOpList [φ] := by
  rw [ofFieldOpList, timeOrder_eq_ι_timeOrderF, timeOrderF_ofFieldOpListF_singleton]

/-- For a field specification `𝓕`, the time order operator acting on a
  list of `𝓕.FieldOp`, `𝓣(φ₀…φₙ)`, is equal to
  `𝓢(φᵢ,φ₀…φᵢ₋₁) • φᵢ * 𝓣(φ₀…φᵢ₋₁φᵢ₊₁φₙ)` where `φᵢ` is the maximal time field
  operator in `φ₀…φₙ`.

  The proof of this result ultimately relies on basic properties of ordering and signs. -/
lemma timeOrder_eq_maxTimeField_mul_finset (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    𝓣(ofFieldOpList (φ :: φs)) = 𝓢(𝓕 |>ₛ maxTimeField φ φs, 𝓕 |>ₛ ⟨(eraseMaxTimeField φ φs).get,
      (Finset.univ.filter (fun x =>
        (maxTimeFieldPosFin φ φs).succAbove x < maxTimeFieldPosFin φ φs))⟩) •
      ofFieldOp (maxTimeField φ φs) * 𝓣(ofFieldOpList (eraseMaxTimeField φ φs)) := by
  rw [ofFieldOpList, timeOrder_eq_ι_timeOrderF, timeOrderF_eq_maxTimeField_mul_finset]
  rfl

lemma timeOrder_superCommute_eq_time_mid {φ ψ : 𝓕.CrAnFieldOp}
    (hφψ : crAnTimeOrderRel φ ψ) (hψφ : crAnTimeOrderRel ψ φ) (a b : 𝓕.WickAlgebra) :
    𝓣(a * [ofCrAnOp φ, ofCrAnOp ψ]ₛ * b) =
    [ofCrAnOp φ, ofCrAnOp ψ]ₛ * 𝓣(a * b) := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  rw [ofCrAnOp, ofCrAnOp, superCommute_eq_ι_superCommuteF, ← map_mul, ← map_mul,
    timeOrder_eq_ι_timeOrderF, ι_timeOrderF_superCommuteF_eq_time hφψ hψφ]
  rfl

lemma timeOrder_superCommute_eq_time_left {φ ψ : 𝓕.CrAnFieldOp}
    (hφψ : crAnTimeOrderRel φ ψ) (hψφ : crAnTimeOrderRel ψ φ) (b : 𝓕.WickAlgebra) :
    𝓣([ofCrAnOp φ, ofCrAnOp ψ]ₛ * b) =
    [ofCrAnOp φ, ofCrAnOp ψ]ₛ * 𝓣(b) := by
  simpa using timeOrder_superCommute_eq_time_mid hφψ hψφ 1 b

lemma timeOrder_superCommute_ne_time {φ ψ : 𝓕.CrAnFieldOp}
    (hφψ : ¬ (crAnTimeOrderRel φ ψ ∧ crAnTimeOrderRel ψ φ)) :
    𝓣([ofCrAnOp φ, ofCrAnOp ψ]ₛ) = 0 := by
  rw [ofCrAnOp, ofCrAnOp, superCommute_eq_ι_superCommuteF, timeOrder_eq_ι_timeOrderF]
  simpa using ι_timeOrderF_superCommuteF_ne_time hφψ 1 1

lemma timeOrder_superCommute_anPart_ofFieldOp_ne_time {φ ψ : 𝓕.FieldOp}
    (hφψ : ¬ (timeOrderRel φ ψ ∧ timeOrderRel ψ φ)) :
    𝓣([anPart φ,ofFieldOp ψ]ₛ) = 0 := by
  rw [ofFieldOp_eq_sum]
  simp only [map_sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  match φ with
  | .inAsymp φ => simp
  | .position φ | .outAsymp φ =>
    simp only [anPart_position, anPart_outAsymp]
    apply timeOrder_superCommute_ne_time
    simp_all [crAnTimeOrderRel]

/-- For a field specification `𝓕`, and `a`, `b`, `c` in `𝓕.WickAlgebra`, then
  `𝓣(a * b * c) = 𝓣(a * 𝓣(b) * c)`. -/
lemma timeOrder_timeOrder_mid (a b c : 𝓕.WickAlgebra) :
    𝓣(a * b * c) = 𝓣(a * 𝓣(b) * c) := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  obtain ⟨c, rfl⟩ := ι_surjective c
  rw [← map_mul, ← map_mul, timeOrder_eq_ι_timeOrderF, timeOrder_eq_ι_timeOrderF,
  ← map_mul, ← map_mul, timeOrder_eq_ι_timeOrderF, timeOrderF_timeOrderF_mid]

lemma timeOrder_timeOrder_left (b c : 𝓕.WickAlgebra) :
    𝓣(b * c) = 𝓣(𝓣(b) * c) := by
  simpa using timeOrder_timeOrder_mid 1 b c

lemma timeOrder_timeOrder_right (a b : 𝓕.WickAlgebra) :
    𝓣(a * b) = 𝓣(a * 𝓣(b)) := by
  simpa using timeOrder_timeOrder_mid a b 1

/-- Time ordering is a projection. -/
lemma timeOrder_timeOrder (a : 𝓕.WickAlgebra) :
    𝓣(𝓣(a)) = 𝓣(a) := by
  simpa using (timeOrder_timeOrder_left a 1).symm

end WickAlgebra
end FieldSpecification
