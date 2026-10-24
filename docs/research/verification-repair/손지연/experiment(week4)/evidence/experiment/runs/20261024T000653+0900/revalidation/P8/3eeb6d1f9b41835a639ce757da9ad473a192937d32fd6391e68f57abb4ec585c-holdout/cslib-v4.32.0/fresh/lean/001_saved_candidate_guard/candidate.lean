/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Languages.CombinatoryLogic.Defs
public import Cslib.Foundations.Relation.Confluence

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
# SKI reduction is confluent

This file proves the **Church-Rosser** theorem for the SKI calculus, that is, if `a ↠ b` and
`a ↠ c`, `b ↠ d` and `c ↠ d` for some term `d`. More strongly (though equivalently), we show
that the relation of having a common reduct is transitive — in the above situation, `a` and `b`,
and `a` and `c` have common reducts, so the result implies the same of `b` and `c`. Note that
`MJoin Red` is symmetric (trivially) and reflexive (since `↠` is), so we in fact show that
`MJoin Red` is an equivalence.

Our proof
follows the method of Tait and Martin-Löf for the lambda calculus, as presented for instance in
Chapter 4 of Peter Selinger's notes:
<https://www.mscs.dal.ca/~selinger/papers/papers/lambdanotes.pdf>.

## Main definitions

- `ParallelReduction` : a relation `⭢ₚ` on terms such that `⭢ ⊆ ⭢ₚ ⊆ ↠`, allowing simultaneous
reduction on the head and tail of a term.

## Main results

- `parallelReduction_diamond` : parallel reduction satisfies the diamond property, that is, it is
confluent in a single step.
- `mJoin_red_equivalence` : by a general result, the diamond property for `⭢ₚ` implies the same
for its reflexive-transitive closure. This closure is exactly `↠`, which implies the
**Church-Rosser** theorem as sketched above.
-/

@[expose] public section

namespace Cslib

namespace SKI

open Red MRed Relation

/-- A reduction step allowing simultaneous reduction of disjoint redexes -/
@[reduction_sys "ₚ"]
inductive ParallelReduction : SKI → SKI → Prop
  /-- Parallel reduction is reflexive, -/
  | refl (a : SKI) : ParallelReduction a a
  /-- Contains `Red`, -/
  | red_I (a : SKI) : ParallelReduction (I ⬝ a) a
  | red_K (a b : SKI) : ParallelReduction (K ⬝ a ⬝ b) a
  | red_S (a b c : SKI) : ParallelReduction (S ⬝ a ⬝ b ⬝ c) (a ⬝ c ⬝ (b ⬝ c))
  /-- and allows simultaneous reduction of disjoint redexes. -/
  | par ⦃a a' b b' : SKI⦄ :
      ParallelReduction a a' → ParallelReduction b b' → ParallelReduction (a ⬝ b) (a' ⬝ b')

/-- The inclusion `⭢ₚ ⊆ ↠` -/
theorem mRed_of_parallelReduction {a a' : SKI} (h : a ⭢ₚ a') : a ↠ a' := by
  cases h
  case refl => exact Relation.ReflTransGen.refl
  case par a a' b b' ha hb =>
    apply parallel_mRed
    · exact mRed_of_parallelReduction ha
    · exact mRed_of_parallelReduction hb
  case red_I => exact Relation.ReflTransGen.single (red_I a')
  case red_K b => exact Relation.ReflTransGen.single (red_K a' b)
  case red_S a b c => exact Relation.ReflTransGen.single (red_S a b c)

/-- The inclusion `⭢ ⊆ ⭢ₚ` -/
theorem parallelReduction_of_red {a a' : SKI} (h : a ⭢ a') : a ⭢ₚ a' := by
  cases h
  case red_S => apply ParallelReduction.red_S
  case red_K => apply ParallelReduction.red_K
  case red_I => apply ParallelReduction.red_I
  case red_head a a' b h =>
    apply ParallelReduction.par
    · exact parallelReduction_of_red h
    · exact ParallelReduction.refl b
  case red_tail a b b' h =>
    apply ParallelReduction.par
    · exact ParallelReduction.refl a
    · exact parallelReduction_of_red h

/-- The inclusions of `mRed_of_parallelReduction` and
`parallelReduction_of_red` imply that `⭢` and `⭢ₚ` have the same reflexive-transitive
closure. -/
theorem reflTransGen_parallelReduction_mRed :
    ReflTransGen ParallelReduction = ReflTransGen Red := by
  ext a b
  constructor
  · apply reflTransGen_le_of_le
    -- TODO: restate `parallelReduction_of_red` and others using `≤`?
    exact @mRed_of_parallelReduction
  · apply Relation.reflTransGen_le_of_le
    exact fun a a' h => Relation.ReflTransGen.single (parallelReduction_of_red h)

/-!
Irreducibility for the (partially applied) primitive combinators.

TODO: possibly these should be proven more generally (in another file) for `↠`.
-/

lemma I_irreducible (a : SKI) (h : I ⭢ₚ a) : a = I := by
  cases h
  rfl

lemma K_irreducible (a : SKI) (h : K ⭢ₚ a) : a = K := by
  cases h
  rfl

lemma Ka_irreducible (a c : SKI) (h : (K ⬝ a) ⭢ₚ c) : ∃ a', a ⭢ₚ a' ∧ c = K ⬝ a' := by
  cases h
  case refl => use a, .refl a
  case par b a' h h' => rw [K_irreducible b h]; use a'

lemma S_irreducible (a : SKI) (h : S ⭢ₚ a) : a = S := by
  cases h
  rfl

lemma Sa_irreducible (a c : SKI) (h : (S ⬝ a) ⭢ₚ c) : ∃ a', a ⭢ₚ a' ∧ c = S ⬝ a' := by
  cases h
  case refl =>
    exact ⟨a, ParallelReduction.refl a, rfl⟩
  case par b a' h h' => rw [S_irreducible b h]; use a'

lemma Sab_irreducible (a b c : SKI) (h : (S ⬝ a ⬝ b) ⭢ₚ c) :
    ∃ a' b', a ⭢ₚ a' ∧ b ⭢ₚ b' ∧ c = S ⬝ a' ⬝ b' := by
  cases h
  case refl => use a, b, .refl a, .refl b
  case par c b' hc hb =>
    let ⟨d, hd⟩ := Sa_irreducible a c hc
    rw [hd.2]
    use d, b', hd.1

#repair_guard "by\n  intro a a₁ a₂ h₁ h₂\n  cases h₁\n  case refl => exact ⟨_, h₂, .refl _⟩\n  case par a a' b b' ha' hb' =>\n    cases h₂\n    case refl => exact ⟨_, .refl _, .par ha' hb'⟩\n    case par a'' b'' ha'' hb'' =>\n      let ⟨_, ha₁, ha₂⟩ := parallelReduction_diamond ha' ha''\n      let ⟨_, hb₁, hb₂⟩ := parallelReduction_diamond hb' hb''\n      exact ⟨_, .par ha₁ hb₁, .par ha₂ hb₂⟩\n    case red_I =>\n      rw [I_irreducible a' ha']\n      exact ⟨_, .red_I b', hb'⟩\n    case red_K =>\n      let ⟨a₂', ha₂', heq⟩ := Ka_irreducible a₂ a' ha'\n      rw [heq]\n      exact ⟨_, .red_K a₂' b', ha₂'⟩\n    case red_S a c =>\n      let ⟨_, _, ha, hc, heq⟩ := Sab_irreducible a c a' ha'\n      rw [heq]\n      exact ⟨_, .red_S .., .par (.par ha hb') (.par hc hb')⟩\n  case red_I =>\n    cases h₂\n    case refl => exact ⟨_, .refl _, .red_I _⟩\n    case par c a₁' hc ha =>\n      rw [I_irreducible c hc]\n      exact ⟨_, ha, .red_I _⟩\n    case red_I => exact ⟨_, .refl _, .refl _⟩\n  case red_K c =>\n    cases h₂\n    case refl => exact ⟨_, .refl _, .red_K _ c⟩\n    case par a' c' ha hc =>\n      let ⟨a₁', ha₁', heq⟩ := Ka_irreducible a₁ a' ha\n      rw [heq]\n      exact ⟨_, ha₁', .red_K a₁' c'⟩\n    case red_K => exact ⟨_, .refl _, .refl _⟩\n  case red_S a b c =>\n    cases h₂\n    case refl => exact ⟨_, .refl _, .red_S ..⟩\n    case par d c' hd hc =>\n      let ⟨_, _, ha, hb, heq⟩ := Sab_irreducible a b d hd\n      rw [heq]\n      exact ⟨_, .par (.par ha hc) (.par hb hc), .red_S ..⟩\n    case red_S => exact ⟨_, .refl _, .refl _⟩"
/--
The key result: the Church-Rosser property holds for `⭢ₚ`. The proof is a lengthy case analysis
on the reductions `a ⭢ₚ a₁` and `a ⭢ₚ a₂`, but is entirely mechanical.
-/
theorem parallelReduction_diamond : Diamond ParallelReduction := by
  sorry


theorem join_parallelReduction_equivalence :
    Equivalence (MJoin ParallelReduction) :=
  Confluent.equivalence_join_reflTransGen <| Diamond.toConfluent parallelReduction_diamond

/-- The **Church-Rosser** theorem in its general form. -/
theorem mJoin_red_equivalence : Equivalence (MJoin Red) := by
  rw [MJoin, ←reflTransGen_parallelReduction_mRed]
  exact join_parallelReduction_equivalence

/-- The **Church-Rosser** theorem in the form it is usually stated. -/
theorem MRed.diamond : Confluent Red := by
  intro a b c hab hac
  apply mJoin_red_equivalence.trans (y := a)
  · exact mJoin_red_equivalence.symm (MJoin.single hab)
  · exact MJoin.single hac

end SKI

end Cslib
