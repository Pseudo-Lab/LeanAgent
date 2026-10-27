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

open Filter Topology Real


#repair_guard "by\n  have h_main : ∀ (d e f : (Fin 9 → ℤ)), ((relation d e) ∧ (relation e f)) → (∀ i : Fin 9, 7 ∣ d i - f i) := by\n    intro d e f h\n    have h₁ : relation d e := h.1\n    have h₂ : relation e f := h.2\n    have h₃ : ∀ (i : Fin 9), 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j)) := by\n      have h₄ : (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j))) := (hrelation d e).mp h₁ |>.2\n      exact h₄\n    have h₄ : ∀ (i : Fin 9), 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then f j else e j)) := by\n      have h₅ : (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then f j else e j))) := (hrelation e f).mp h₂ |>.2\n      exact h₅\n    \n    have h₅ : ∀ (i : Fin 9), 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := by\n      intro i\n      have h₆ : 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j)) := h₃ i\n      have h₇ : (digits_to_num (fun j : Fin 9 => if j = i then e j else d j)) = digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n        calc\n          (digits_to_num (fun j : Fin 9 => if j = i then e j else d j)) = ∑ j : Fin 9, (if j = i then e j else d j) * (10 : ℤ) ^ (j : ℕ) := by\n            simp [hdigits_to_num]\n            <;>\n            rfl\n          _ = ∑ j : Fin 9, (if j = i then e j else d j) * (10 : ℤ) ^ (j : ℕ) := rfl\n          _ = (∑ j : Fin 9, d j * (10 : ℤ) ^ (j : ℕ)) + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n            calc\n              (∑ j : Fin 9, (if j = i then e j else d j) * (10 : ℤ) ^ (j : ℕ)) = ∑ j : Fin 9, (d j * (10 : ℤ) ^ (j : ℕ) + (if j = i then (e j - d j) else 0) * (10 : ℤ) ^ (j : ℕ)) := by\n                apply Finset.sum_congr rfl\n                intro j _\n                by_cases h : j = i\n                · simp [h]\n                  <;> ring\n                · simp [h]\n                  <;> ring\n              _ = (∑ j : Fin 9, d j * (10 : ℤ) ^ (j : ℕ)) + ∑ j : Fin 9, (if j = i then (e j - d j) else 0) * (10 : ℤ) ^ (j : ℕ) := by\n                rw [Finset.sum_add_distrib]\n              _ = (∑ j : Fin 9, d j * (10 : ℤ) ^ (j : ℕ)) + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n                have h₈ : ∑ j : Fin 9, (if j = i then (e j - d j) else 0) * (10 : ℤ) ^ (j : ℕ) = (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n                  calc\n                    _ = ∑ j : Fin 9, (if j = i then (e j - d j) else 0) * (10 : ℤ) ^ (j : ℕ) := rfl\n                    _ = (if i = i then (e i - d i) else 0) * (10 : ℤ) ^ (i : ℕ) := by\n                      simp [Finset.sum_ite_eq', Finset.mem_univ, i.is_lt]\n                    _ = (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by simp\n                rw [h₈]\n                <;> simp [hdigits_to_num]\n                <;>\n                rfl\n          _ = digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n            simp [hdigits_to_num]\n            <;>\n            rfl\n      have h₈ : 7 ∣ digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n        rw [h₇] at h₆\n        exact h₆\n      have h₉ : 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := by\n        have h₁₀ : (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d = digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by ring\n        rw [h₁₀]\n        exact h₈\n      exact h₉\n    \n    have h₆ : ∀ (i : Fin 9), 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e := by\n      intro i\n      have h₇ : 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then f j else e j)) := h₄ i\n      have h₈ : (digits_to_num (fun j : Fin 9 => if j = i then f j else e j)) = digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by\n        calc\n          (digits_to_num (fun j : Fin 9 => if j = i then f j else e j)) = ∑ j : Fin 9, (if j = i then f j else e j) * (10 : ℤ) ^ (j : ℕ) := by\n            simp [hdigits_to_num]\n            <;>\n            rfl\n          _ = ∑ j : Fin 9, (if j = i then f j else e j) * (10 : ℤ) ^ (j : ℕ) := rfl\n          _ = (∑ j : Fin 9, e j * (10 : ℤ) ^ (j : ℕ)) + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by\n            calc\n              (∑ j : Fin 9, (if j = i then f j else e j) * (10 : ℤ) ^ (j : ℕ)) = ∑ j : Fin 9, (e j * (10 : ℤ) ^ (j : ℕ) + (if j = i then (f j - e j) else 0) * (10 : ℤ) ^ (j : ℕ)) := by\n                apply Finset.sum_congr rfl\n                intro j _\n                by_cases h : j = i\n                · simp [h]\n                  <;> ring\n                · simp [h]\n                  <;> ring\n              _ = (∑ j : Fin 9, e j * (10 : ℤ) ^ (j : ℕ)) + ∑ j : Fin 9, (if j = i then (f j - e j) else 0) * (10 : ℤ) ^ (j : ℕ) := by\n                rw [Finset.sum_add_distrib]\n              _ = (∑ j : Fin 9, e j * (10 : ℤ) ^ (j : ℕ)) + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by\n                have h₉ : ∑ j : Fin 9, (if j = i then (f j - e j) else 0) * (10 : ℤ) ^ (j : ℕ) = (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by\n                  calc\n                    _ = ∑ j : Fin 9, (if j = i then (f j - e j) else 0) * (10 : ℤ) ^ (j : ℕ) := rfl\n                    _ = (if i = i then (f i - e i) else 0) * (10 : ℤ) ^ (i : ℕ) := by\n                      simp [Finset.sum_ite_eq', Finset.mem_univ, i.is_lt]\n                    _ = (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by simp\n                rw [h₉]\n                <;> simp [hdigits_to_num]\n                <;>\n                rfl\n          _ = digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by\n            simp [hdigits_to_num]\n            <;>\n            rfl\n      have h₉ : 7 ∣ digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by\n        rw [h₈] at h₇\n        exact h₇\n      have h₁₀ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e := by\n        have h₁₁ : (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e = digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by ring\n        rw [h₁₁]\n        exact h₉\n      exact h₁₀\n    \n    have h₇ : 7 ∣ digits_to_num e + digits_to_num d := by\n      have h₈ : digits_to_num e = digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n        calc\n          digits_to_num e = ∑ i : Fin 9, e i * (10 : ℤ) ^ (i : ℕ) := by simp [hdigits_to_num]\n          _ = ∑ i : Fin 9, (d i + (e i - d i)) * (10 : ℤ) ^ (i : ℕ) := by\n            apply Finset.sum_congr rfl\n            intro i _\n            ring\n          _ = ∑ i : Fin 9, (d i * (10 : ℤ) ^ (i : ℕ) + (e i - d i) * (10 : ℤ) ^ (i : ℕ)) := by\n            apply Finset.sum_congr rfl\n            intro i _\n            ring\n          _ = (∑ i : Fin 9, d i * (10 : ℤ) ^ (i : ℕ)) + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n            rw [Finset.sum_add_distrib]\n          _ = digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n            simp [hdigits_to_num]\n            <;>\n            rfl\n      have h₉ : ∀ i : Fin 9, 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := h₅\n      have h₁₀ : 7 ∣ ∑ i : Fin 9, ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) := by\n        apply Finset.dvd_sum\n        intro i _\n        exact h₉ i\n      have h₁₁ : ∑ i : Fin 9, ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) = ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + 9 * digits_to_num d := by\n        calc\n          ∑ i : Fin 9, ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) = ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + ∑ i : Fin 9, digits_to_num d := by\n            rw [Finset.sum_add_distrib]\n          _ = ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + 9 * digits_to_num d := by\n            simp [Finset.sum_const, Finset.card_fin]\n            <;> ring\n            <;> norm_num\n      have h₁₂ : 7 ∣ ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + 9 * digits_to_num d := by\n        rw [h₁₁] at h₁₀\n        exact h₁₀\n      have h₁₃ : 7 ∣ digits_to_num e + digits_to_num d := by\n        have h₁₄ : digits_to_num e + digits_to_num d = 2 * digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n          linarith\n        rw [h₁₄]\n        have h₁₅ : 7 ∣ 2 * digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n          have h₁₆ : 7 ∣ ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + 9 * digits_to_num d := h₁₂\n          have h₁₇ : 7 ∣ 2 * digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n            have h₁₈ : (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + 9 * digits_to_num d) = (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 9 * digits_to_num d := by ring\n            rw [h₁₈] at h₁₆\n            have h₁₉ : 7 ∣ (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 2 * digits_to_num d := by\n              have h₂₀ : 7 ∣ (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 9 * digits_to_num d := h₁₆\n              have h₂₁ : 7 ∣ 7 * digits_to_num d := by\n                use digits_to_num d\n                <;> ring\n              have h₂₂ : 7 ∣ (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 2 * digits_to_num d := by\n                have h₂₃ : (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 2 * digits_to_num d = ((∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 9 * digits_to_num d) - 7 * digits_to_num d := by ring\n                rw [h₂₃]\n                exact dvd_sub h₂₀ h₂₁\n              exact h₂₂\n            have h₂₀ : 7 ∣ 2 * digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n              have h₂₁ : 2 * digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) = (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 2 * digits_to_num d := by ring\n              rw [h₂₁]\n              exact h₁₉\n            exact h₂₀\n          exact h₁₇\n        exact h₁₅\n      exact h₁₃\n    \n    have h₈ : ∀ (i : Fin 9), 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n      intro i\n      have h₉ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e := h₆ i\n      have h₁₀ : 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := h₅ i\n      have h₁₁ : 7 ∣ digits_to_num e + digits_to_num d := h₇\n      have h₁₂ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d := by\n        have h₁₃ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e := h₆ i\n        have h₁₄ : 7 ∣ digits_to_num e + digits_to_num d := h₇\n        have h₁₅ : 7 ∣ ((f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e) - (digits_to_num e + digits_to_num d) := by\n          exact dvd_sub h₁₃ h₁₄\n        have h₁₆ : ((f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e) - (digits_to_num e + digits_to_num d) = (f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d := by\n          ring\n        rw [h₁₆] at h₁₅\n        exact h₁₅\n      have h₁₃ : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n        have h₁₄ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d := h₁₂\n        have h₁₅ : 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := h₅ i\n        have h₁₆ : 7 ∣ ((f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d) + ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) := by\n          exact dvd_add h₁₄ h₁₅\n        have h₁₇ : ((f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d) + ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) = (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n          ring\n        rw [h₁₇] at h₁₆\n        exact h₁₆\n      exact h₁₃\n    \n    have h₉ : ∀ (i : Fin 9), 7 ∣ d i - f i := by\n      intro i\n      have h₁₀ : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := h₈ i\n      have h₁₁ : 7 ∣ (f i - d i) := by\n        have h₁₂ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := h₁₀\n        have h₁₃ : (7 : ℕ).Prime := by decide\n        have h₁₄ : ¬(7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by\n          intro h\n          have h₁₅ : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by\n            norm_cast at h ⊢\n            <;> simpa [Int.coe_nat_dvd_left] using h\n          have h₁₆ : (7 : ℕ) ∣ 10 := by\n            exact Nat.Prime.dvd_of_dvd_pow h₁₃ h₁₅\n          norm_num at h₁₆\n          <;> contradiction\n        have h₁₅ : (7 : ℤ) ∣ (f i - d i) := by\n          have h₁₆ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := h₁₂\n          have h₁₇ : ¬(7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := h₁₄\n          have h₁₈ : (7 : ℤ) ∣ (f i - d i) := by\n            have h₁₉ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := h₁₂\n            have h₂₀ : (7 : ℕ).Prime := by decide\n            have h₂₁ : (7 : ℤ) ∣ (f i - d i) ∨ (7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by\n              have h₂₂ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := h₁₂\n              have h₂₃ : (7 : ℤ) ∣ (f i - d i) ∨ (7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by\n                apply (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp\n                exact h₂₂\n              exact h₂₃\n            cases h₂₁ with\n            | inl h₂₁ =>\n              exact h₂₁\n            | inr h₂₁ =>\n              exfalso\n              exact h₁₄ h₂₁\n          exact h₁₈\n        exact h₁₅\n      have h₁₂ : 7 ∣ d i - f i := by\n        have h₁₃ : 7 ∣ (f i - d i) := h₁₁\n        have h₁₄ : 7 ∣ -(f i - d i) := by\n          exact dvd_neg.mpr h₁₃\n        have h₁₅ : -(f i - d i) = d i - f i := by ring\n        rw [h₁₅] at h₁₄\n        exact h₁₄\n      exact h₁₂\n    intro i\n    have h₁₀ : 7 ∣ d i - f i := h₉ i\n    exact h₁₀\n  exact h_main"
theorem putnam_1995_a3
(relation : (Fin 9 → ℤ) → (Fin 9 → ℤ) → Prop)
(digits_to_num : (Fin 9 → ℤ) → ℤ)
(hdigits_to_num : digits_to_num = fun dig => ∑ i : Fin 9, (dig i) * 10^i.1)
(hrelation : ∀ d e : (Fin 9 → ℤ), relation d e ↔ (∀ i : Fin 9, d i < 10 ∧ d i ≥ 0 ∧ e i < 10 ∧ e i ≥ 0) ∧ (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j))))
: ∀ d e f : (Fin 9 → ℤ), ((relation d e) ∧ (relation e f)) → (∀ i : Fin 9, 7 ∣ d i - f i) := by
  sorry

