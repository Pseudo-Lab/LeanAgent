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


#repair_guard "by\n  classical\n  intro d e f h i\n  have hdiff (a b : Fin 9 → ℤ) :\n      digits_to_num b - digits_to_num a =\n        ∑ j : Fin 9, (b j - a j) * (10 : ℤ) ^ (j : ℕ) := by\n    rw [hdigits_to_num, ← Finset.sum_sub_distrib]\n    apply Finset.sum_congr rfl\n    intro j _\n    ring\n  have hrepl (a b : Fin 9 → ℤ) (k : Fin 9) :\n      digits_to_num (fun j : Fin 9 => if j = k then b j else a j) =\n        digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by\n    rw [hdigits_to_num]\n    calc\n      (∑ j : Fin 9, (if j = k then b j else a j) * (10 : ℤ) ^ (j : ℕ)) =\n          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +\n            if j = k then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0) := by\n        apply Finset.sum_congr rfl\n        intro j _\n        by_cases hj : j = k\n        · subst j\n          simp only [if_pos]\n          ring\n        · simp [hj]\n      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +\n          (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by\n        rw [Finset.sum_add_distrib]\n        simp [Finset.sum_ite_eq', Finset.mem_univ]\n  have hrepdvd (a b : Fin 9 → ℤ) (hab : relation a b) (k : Fin 9) :\n      7 ∣ digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by\n    rw [← hrepl a b k]\n    exact ((hrelation a b).mp hab).2 k\n  have hsum (a b : Fin 9 → ℤ) (hab : relation a b) :\n      7 ∣ digits_to_num a + digits_to_num b := by\n    have hs : 7 ∣ ∑ k : Fin 9,\n        (digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ)) := by\n      apply Finset.dvd_sum\n      intro k _\n      exact hrepdvd a b hab k\n    have heq :\n        (∑ k : Fin 9,\n          (digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ))) =\n          digits_to_num a + digits_to_num b + 7 * digits_to_num a := by\n      rw [Finset.sum_add_distrib, ← hdiff a b]\n      simp\n      ring\n    rw [heq] at hs\n    convert dvd_sub hs ⟨digits_to_num a, rfl⟩ using 1 <;> ring\n  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by\n    have hs := dvd_sub\n      (dvd_add (hrepdvd d e h.1 i) (hrepdvd e f h.2 i))\n      (hsum d e h.1)\n    convert hs using 1 <;> ring\n  have hprime : Prime (7 : ℤ) :=\n    Int.prime_iff_natAbs_prime.mpr (by decide)\n  rcases hprime.dvd_mul.mp hp with hfd | hpow\n  · simpa only [neg_sub] using dvd_neg.mpr hfd\n  · exfalso\n    have hpow' : (7 : ℕ) ∣ 10 ^ (i : ℕ) := by\n      norm_cast at hpow ⊢\n    have hten : (7 : ℕ) ∣ 10 :=\n      (by decide : Nat.Prime 7).dvd_of_dvd_pow hpow'\n    norm_num at hten"
theorem putnam_1995_a3
(relation : (Fin 9 → ℤ) → (Fin 9 → ℤ) → Prop)
(digits_to_num : (Fin 9 → ℤ) → ℤ)
(hdigits_to_num : digits_to_num = fun dig => ∑ i : Fin 9, (dig i) * 10^i.1)
(hrelation : ∀ d e : (Fin 9 → ℤ), relation d e ↔ (∀ i : Fin 9, d i < 10 ∧ d i ≥ 0 ∧ e i < 10 ∧ e i ≥ 0) ∧ (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j))))
: ∀ d e f : (Fin 9 → ℤ), ((relation d e) ∧ (relation e f)) → (∀ i : Fin 9, 7 ∣ d i - f i) := by
  sorry

