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


#repair_measure
theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  rcases boundedu with ⟨B, T, hBT⟩
  have hr : (Set.range u).Finite := by
    apply (Set.finite_Icc B T).subset
    rintro _ ⟨n, rfl⟩
    exact hBT n
  let v : ℕ → (ℤ × ℤ) × (ℤ × ℤ) :=
    fun n => ((u n, u (n + 1)), (u (n + 2), u (n + 3)))
  have hv : (Set.range v).Finite := by
    apply ((hr.prod hr).prod (hr.prod hr)).subset
    rintro _ ⟨n, rfl⟩
    exact
      ⟨⟨⟨n, rfl⟩, ⟨n + 1, rfl⟩⟩,
       ⟨⟨n + 2, rfl⟩, ⟨n + 3, rfl⟩⟩⟩
  have periodic_of_state :
      ∀ {a b : ℕ}, a < b → v a = v b →
        ∃ c : ℕ, c > 0 ∧ ∀ n ≥ a, u (n + c) = u n := by
    intro a b hab hstate
    have h0 : u a = u b := by
      simpa [v] using
        congrArg (fun x : (ℤ × ℤ) × (ℤ × ℤ) => x.1.1) hstate
    have h1 : u (a + 1) = u (b + 1) := by
      simpa [v] using
        congrArg (fun x : (ℤ × ℤ) × (ℤ × ℤ) => x.1.2) hstate
    have h2 : u (a + 2) = u (b + 2) := by
      simpa [v] using
        congrArg (fun x : (ℤ × ℤ) × (ℤ × ℤ) => x.2.1) hstate
    have h3 : u (a + 3) = u (b + 3) := by
      simpa [v] using
        congrArg (fun x : (ℤ × ℤ) × (ℤ × ℤ) => x.2.2) hstate
    let c : ℕ := b - a
    have hc : c > 0 := by
      dsimp [c]
      omega
    have hac : a + c = b := by
      dsimp [c]
      omega
    refine ⟨c, hc, ?_⟩
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hna
        by_cases hnsmall : n < a + 4
        · have hcases :
              n = a ∨ n = a + 1 ∨ n = a + 2 ∨ n = a + 3 := by
            omega
          rcases hcases with rfl | rfl | rfl | rfl
          · rw [hac]
            exact h0.symm
          · have hi : a + 1 + c = b + 1 := by omega
            rw [hi]
            exact h1.symm
          · have hi : a + 2 + c = b + 2 := by omega
            rw [hi]
            exact h2.symm
          · have hi : a + 3 + c = b + 3 := by omega
            rw [hi]
            exact h3.symm
        · have hu1 : u ((n - 1) + c) = u (n - 1) :=
            ih (n - 1) (by omega) (by omega)
          have hu2 : u ((n - 2) + c) = u (n - 2) :=
            ih (n - 2) (by omega) (by omega)
          have hu3 : u ((n - 3) + c) = u (n - 3) :=
            ih (n - 3) (by omega) (by omega)
          have hu4 : u ((n - 4) + c) = u (n - 4) :=
            ih (n - 4) (by omega) (by omega)
          have hi1 : n + c - 1 = (n - 1) + c := by omega
          have hi2 : n + c - 2 = (n - 2) + c := by omega
          have hi3 : n + c - 3 = (n - 3) + c := by omega
          have hi4 : n + c - 4 = (n - 4) + c := by omega
          have hnc := (hu (n + c) (by omega)).1
          have hn := (hu n (by omega)).1
          rw [hi1, hi2, hi3, hi4, hu1, hu2, hu3, hu4] at hnc
          have hreal : (u (n + c) : ℝ) = u n := hnc.trans hn.symm
          exact_mod_cast hreal
  obtain ⟨a, b, hab, hstate⟩ :=
    hv.exists_ne_map_eq_of_infinite
      (fun n : ℕ => ⟨v n, Set.mem_range_self n⟩)
  have hstate' : v a = v b :=
    congrArg (fun z : Set.range v => z.1) hstate
  rcases lt_or_gt_of_ne hab with hab' | hba
  · obtain ⟨c, hc, hp⟩ := periodic_of_state hab' hstate'
    exact ⟨a, c, hc, hp⟩
  · obtain ⟨c, hc, hp⟩ := periodic_of_state hba hstate'.symm
    exact ⟨b, c, hc, hp⟩

#check _root_.putnam_1964_a4
#print axioms _root_.putnam_1964_a4
