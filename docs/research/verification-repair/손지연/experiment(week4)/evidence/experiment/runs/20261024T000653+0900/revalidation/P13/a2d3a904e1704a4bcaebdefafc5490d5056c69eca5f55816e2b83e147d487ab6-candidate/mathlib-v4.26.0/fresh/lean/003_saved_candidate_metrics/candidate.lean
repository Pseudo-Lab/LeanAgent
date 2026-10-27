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
  classical
  rcases boundedu with ⟨B, T, hbounds⟩
  let S : Set ℤ := Set.Icc B T
  letI : Fintype S := (Set.finite_Icc B T).fintype
  let f : ℕ → (Fin 4 → S) := fun n i =>
    ⟨u (n + i), hbounds (n + i)⟩
  obtain ⟨a, b, hab, hfab⟩ :=
    Finite.exists_ne_map_eq_of_infinite f
  have hpq : ∃ p q : ℕ, p < q ∧ f p = f q := by
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact ⟨a, b, hlt, hfab⟩
    · exact ⟨b, a, hgt, hfab.symm⟩
  rcases hpq with ⟨p, q, hpq, hstate⟩
  let c := q - p
  have hc : p + c = q := by
    dsimp [c]
    omega
  have hcpos : 0 < c := by
    dsimp [c]
    omega
  have hbase : ∀ i : Fin 4, u (p + (i : ℕ)) = u (q + (i : ℕ)) := by
    intro i
    simpa [f] using
      congrArg (fun g : Fin 4 → S => (g i : ℤ)) hstate
  have hperiod : ∀ k : ℕ, u (p + k + c) = u (p + k) := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih
    by_cases hk : k < 4
    · have h := hbase ⟨k, hk⟩
      have hidx : p + k + c = q + k := by omega
      rw [hidx]
      exact h.symm
    · have hk4 : 4 ≤ k := by omega
      have h1 := ih (k - 1) (by omega)
      have h2 := ih (k - 2) (by omega)
      have h3 := ih (k - 3) (by omega)
      have h4 := ih (k - 4) (by omega)
      have e1 : u ((p + k + c) - 1) = u ((p + k) - 1) := by
        have hl : (p + k + c) - 1 = p + (k - 1) + c := by omega
        have hr : (p + k) - 1 = p + (k - 1) := by omega
        calc
          u ((p + k + c) - 1) = u (p + (k - 1) + c) := by rw [hl]
          _ = u (p + (k - 1)) := h1
          _ = u ((p + k) - 1) := by rw [hr]
      have e2 : u ((p + k + c) - 2) = u ((p + k) - 2) := by
        have hl : (p + k + c) - 2 = p + (k - 2) + c := by omega
        have hr : (p + k) - 2 = p + (k - 2) := by omega
        calc
          u ((p + k + c) - 2) = u (p + (k - 2) + c) := by rw [hl]
          _ = u (p + (k - 2)) := h2
          _ = u ((p + k) - 2) := by rw [hr]
      have e3 : u ((p + k + c) - 3) = u ((p + k) - 3) := by
        have hl : (p + k + c) - 3 = p + (k - 3) + c := by omega
        have hr : (p + k) - 3 = p + (k - 3) := by omega
        calc
          u ((p + k + c) - 3) = u (p + (k - 3) + c) := by rw [hl]
          _ = u (p + (k - 3)) := h3
          _ = u ((p + k) - 3) := by rw [hr]
      have e4 : u ((p + k + c) - 4) = u ((p + k) - 4) := by
        have hl : (p + k + c) - 4 = p + (k - 4) + c := by omega
        have hr : (p + k) - 4 = p + (k - 4) := by omega
        calc
          u ((p + k + c) - 4) = u (p + (k - 4) + c) := by rw [hl]
          _ = u (p + (k - 4)) := h4
          _ = u ((p + k) - 4) := by rw [hr]
      have hleft := (hu (p + k + c) (by omega)).1
      have hright := (hu (p + k) (by omega)).1
      rw [e1, e2, e3, e4] at hleft
      have hcast : (u (p + k + c) : ℝ) = (u (p + k) : ℝ) :=
        hleft.trans hright.symm
      exact_mod_cast hcast
  refine ⟨p, c, hcpos, ?_⟩
  intro n hn
  have h := hperiod (n - p)
  have hnp : p + (n - p) = n := by omega
  rw [hnp] at h
  exact h

#check _root_.putnam_1964_a4
#print axioms _root_.putnam_1964_a4
