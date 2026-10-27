import Mathlib
import Aesop

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

set_option maxHeartbeats 0

open Set Function


#repair_guard "by\n  classical\n  obtain ⟨B, T, hB⟩ := boundedu\n  let f : ℕ → (ℤ × ℤ × ℤ × ℤ) :=\n    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))\n  have hfin : Set.Finite (Set.range f) := by\n    apply Set.Finite.subset\n      (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))\n    rintro _ ⟨n, rfl⟩\n    have h₀ := hB n\n    have h₁ := hB (n + 1)\n    have h₂ := hB (n + 2)\n    have h₃ := hB (n + 3)\n    simp only [Finset.mem_Icc, Prod.le_def] at *\n    simp_all [f]\n  have hpigeon : ∃ i j : ℕ, i < j ∧ f i = f j := by\n    by_contra! h\n    have hinj : Function.Injective f := by\n      intro i j hij\n      rcases lt_trichotomy i j with hlt | rfl | hgt\n      · exact (h i j hlt hij).elim\n      · rfl\n      · exact (h j i hgt hij.symm).elim\n    exact Set.not_infinite.mpr hfin (Set.infinite_range_of_injective hinj)\n  obtain ⟨i, j, hij, hf⟩ := hpigeon\n  have heq :\n      u i = u j ∧ u (i + 1) = u (j + 1) ∧\n        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by\n    simpa [f] using hf\n  have hall : ∀ m : ℕ, u (i + m) = u (j + m) := by\n    intro m\n    induction m using Nat.strong_induction_on with\n    | h m ih =>\n        match m with\n        | 0 => simpa using heq.1\n        | 1 => simpa using heq.2.1\n        | 2 => simpa using heq.2.2.1\n        | 3 => simpa using heq.2.2.2\n        | m + 4 =>\n          have hi := (hu (i + (m + 4)) (by omega)).1\n          have hj := (hu (j + (m + 4)) (by omega)).1\n          have h₁ : i + (m + 4) - 1 = i + (m + 3) := by omega\n          have h₂ : i + (m + 4) - 2 = i + (m + 2) := by omega\n          have h₃ : i + (m + 4) - 3 = i + (m + 1) := by omega\n          have h₄ : i + (m + 4) - 4 = i + m := by omega\n          have h₅ : j + (m + 4) - 1 = j + (m + 3) := by omega\n          have h₆ : j + (m + 4) - 2 = j + (m + 2) := by omega\n          have h₇ : j + (m + 4) - 3 = j + (m + 1) := by omega\n          have h₈ : j + (m + 4) - 4 = j + m := by omega\n          simp only [h₁, h₂, h₃, h₄] at hi\n          simp only [h₅, h₆, h₇, h₈] at hj\n          have h₉ := ih (m + 3) (by omega)\n          have h₁₀ := ih (m + 2) (by omega)\n          have h₁₁ := ih (m + 1) (by omega)\n          have h₁₂ := ih m (by omega)\n          rw [h₉, h₁₀, h₁₁, h₁₂] at hi\n          exact_mod_cast hi.trans hj.symm\n  refine ⟨i, j - i, by omega, ?_⟩\n  intro n hn\n  calc\n    u (n + (j - i)) = u (j + (n - i)) := congrArg u (by omega)\n    _ = u (i + (n - i)) := (hall (n - i)).symm\n    _ = u n := congrArg u (by omega)"
theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  sorry

