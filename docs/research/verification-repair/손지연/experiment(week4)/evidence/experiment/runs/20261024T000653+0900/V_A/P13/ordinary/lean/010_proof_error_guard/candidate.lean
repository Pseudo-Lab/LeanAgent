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


#repair_guard "by \n  have h_main : ∃ (i j : ℕ), i < j ∧ (u i = u j ∧ u (i + 1) = u (j + 1) ∧ u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3)) := by\n    obtain ⟨B, T, hB⟩ := boundedu\n    have h₁ : ∃ (i j : ℕ), i < j ∧ (u i = u j ∧ u (i + 1) = u (j + 1) ∧ u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3)) := by\n      \n      classical\n      \n      let f : ℕ → (ℤ × ℤ × ℤ × ℤ) := fun n => (u n, u (n + 1), u (n + 2), u (n + 3))\n      have h₂ : Set.Finite (Set.range f) := by\n        have h₃ : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by\n          intro x hx\n          rcases hx with ⟨n, rfl⟩\n          have h₄ := hB n\n          have h₅ := hB (n + 1)\n          have h₆ := hB (n + 2)\n          have h₇ := hB (n + 3)\n          simp only [Set.mem_Icc, Prod.le_def] at h₄ h₅ h₆ h₇ ⊢\n          constructor <;>\n          (try constructor) <;>\n          (try constructor) <;>\n          (try constructor) <;>\n          (try simp_all [f]) <;>\n          (try nlinarith)\n        \n        have h₄ : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by\n          exact experiment_missing_lemma\n          intro x hx\n          simp_all [Set.mem_Icc]\n          <;>\n          (try aesop)\n        exact Set.Finite.subset h₄ h₃\n      \n      have h₃ : ∃ (i j : ℕ), i < j ∧ f i = f j := by\n        by_contra! h₄\n        have h₅ : Function.Injective f := by\n          intro i j h₆\n          by_cases h₇ : i = j\n          · exact h₇\n          · have h₈ : i < j ∨ j < i := by omega\n            cases h₈ with\n            | inl h₈ =>\n              have h₉ := h₄ i j h₈\n              simp_all\n            | inr h₈ =>\n              have h₉ := h₄ j i h₈\n              simp_all\n        have h₆ : Set.Infinite (Set.range f) := Set.infinite_range_of_injective h₅\n        exact Set.not_infinite.mpr h₂ h₆\n      \n      obtain ⟨i, j, h₄, h₅⟩ := h₃\n      refine' ⟨i, j, h₄, _⟩\n      simp [f] at h₅ ⊢\n      <;>\n      (try simp_all [Prod.ext_iff]) <;>\n      (try omega) <;>\n      (try aesop)\n    exact h₁\n  \n  have h_periodic : ∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n := by\n    obtain ⟨i, j, hij, h_eq⟩ := h_main\n    have h₁ : ∀ m : ℕ, u (i + m) = u (j + m) := by\n      intro m\n      have h₂ : ∀ m : ℕ, u (i + m) = u (j + m) := by\n        intro m\n        induction m using Nat.strong_induction_on with\n        | h m ih =>\n          match m with\n          | 0 =>\n            have h₃ := h_eq.1\n            simp at h₃ ⊢\n            <;> simp_all [add_assoc]\n          | 1 =>\n            have h₃ := h_eq.2.1\n            simp at h₃ ⊢\n            <;> simp_all [add_assoc]\n            <;> ring_nf at *\n            <;> omega\n          | 2 =>\n            have h₃ := h_eq.2.2.1\n            simp at h₃ ⊢\n            <;> simp_all [add_assoc]\n            <;> ring_nf at *\n            <;> omega\n          | 3 =>\n            have h₃ := h_eq.2.2.2\n            simp at h₃ ⊢\n            <;> simp_all [add_assoc]\n            <;> ring_nf at *\n            <;> omega\n          | m + 4 =>\n            have h₃ : i + (m + 4) ≥ 4 := by\n              have h₄ : i ≥ 0 := by linarith\n              omega\n            have h₄ : u (i + (m + 4)) = ((u (i + (m + 4) - 1) + u (i + (m + 4) - 2) + u (i + (m + 4) - 3) * u (i + (m + 4) - 4)) : ℝ) / (u (i + (m + 4) - 1) * u (i + (m + 4) - 2) + u (i + (m + 4) - 3) + u (i + (m + 4) - 4)) := by\n              have h₅ := hu (i + (m + 4)) (by omega)\n              have h₆ := h₅.1\n              norm_cast at h₆ ⊢\n              <;> simp_all [add_assoc]\n              <;> ring_nf at *\n              <;> norm_num at *\n              <;> linarith\n            have h₅ : u (j + (m + 4)) = ((u (j + (m + 4) - 1) + u (j + (m + 4) - 2) + u (j + (m + 4) - 3) * u (j + (m + 4) - 4)) : ℝ) / (u (j + (m + 4) - 1) * u (j + (m + 4) - 2) + u (j + (m + 4) - 3) + u (j + (m + 4) - 4)) := by\n              have h₆ := hu (j + (m + 4)) (by\n                have h₇ : j ≥ i + 1 := by omega\n                omega\n              )\n              have h₇ := h₆.1\n              norm_cast at h₇ ⊢\n              <;> simp_all [add_assoc]\n              <;> ring_nf at *\n              <;> norm_num at *\n              <;> linarith\n            have h₆ : (i + (m + 4) - 1 : ℕ) = i + (m + 3) := by\n              omega\n            have h₇ : (i + (m + 4) - 2 : ℕ) = i + (m + 2) := by\n              omega\n            have h₈ : (i + (m + 4) - 3 : ℕ) = i + (m + 1) := by\n              omega\n            have h₉ : (i + (m + 4) - 4 : ℕ) = i + m := by\n              omega\n            have h₁₀ : (j + (m + 4) - 1 : ℕ) = j + (m + 3) := by\n              omega\n            have h₁₁ : (j + (m + 4) - 2 : ℕ) = j + (m + 2) := by\n              omega\n            have h₁₂ : (j + (m + 4) - 3 : ℕ) = j + (m + 1) := by\n              omega\n            have h₁₃ : (j + (m + 4) - 4 : ℕ) = j + m := by\n              omega\n            have h₁₄ : u (i + (m + 3)) = u (j + (m + 3)) := by\n              have h₁₅ := ih (m + 3) (by omega)\n              simp [add_assoc] at h₁₅ ⊢\n              <;> omega\n            have h₁₅ : u (i + (m + 2)) = u (j + (m + 2)) := by\n              have h₁₆ := ih (m + 2) (by omega)\n              simp [add_assoc] at h₁₆ ⊢\n              <;> omega\n            have h₁₆ : u (i + (m + 1)) = u (j + (m + 1)) := by\n              have h₁₇ := ih (m + 1) (by omega)\n              simp [add_assoc] at h₁₇ ⊢\n              <;> omega\n            have h₁₇ : u (i + m) = u (j + m) := by\n              have h₁₈ := ih m (by omega)\n              simp [add_assoc] at h₁₈ ⊢\n              <;> omega\n            have h₁₈ : (u (i + (m + 4)) : ℝ) = (u (j + (m + 4)) : ℝ) := by\n              rw [h₄, h₅]\n              simp [h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃] at *\n              norm_cast at *\n              <;>\n              (try simp_all [h₁₄, h₁₅, h₁₆, h₁₇]) <;>\n              (try ring_nf at *) <;>\n              (try field_simp at *) <;>\n              (try norm_cast at *) <;>\n              (try linarith)\n            norm_cast at h₁₈ ⊢\n            <;>\n            (try simp_all) <;>\n            (try linarith)\n      exact h₂ m\n    have h₂ : ∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n := by\n      use i, (j - i)\n      have h₃ : j - i > 0 := by\n        omega\n      constructor\n      · exact h₃\n      · intro n hn\n        have h₄ : u (n + (j - i)) = u n := by\n          have h₅ : u (i + (n - i)) = u (j + (n - i)) := by\n            have h₆ := h₁ (n - i)\n            simp [add_assoc] at h₆ ⊢\n            <;> omega\n          have h₆ : i + (n - i) = n := by\n            omega\n          have h₇ : j + (n - i) = n + (j - i) := by\n            omega\n          rw [h₆] at h₅\n          rw [h₇] at h₅\n          linarith\n        exact h₄\n    exact h₂\n  \n  exact h_periodic"
theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  sorry

