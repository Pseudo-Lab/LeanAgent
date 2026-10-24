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
  have h_main : ∃ (i j : ℕ), i < j ∧ (u i = u j ∧ u (i + 1) = u (j + 1) ∧ u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3)) := by
    obtain ⟨B, T, hB⟩ := boundedu
    have h₁ : ∃ (i j : ℕ), i < j ∧ (u i = u j ∧ u (i + 1) = u (j + 1) ∧ u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3)) := by
      classical
      let f : ℕ → (ℤ × ℤ × ℤ × ℤ) := fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
      have h₂ : Set.Finite (Set.range f) := by
        have h₃ : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
          intro x hx
          rcases hx with ⟨n, rfl⟩
          have h₄ := hB n
          have h₅ := hB (n + 1)
          have h₆ := hB (n + 2)
          have h₇ := hB (n + 3)
          simp only [Set.mem_Icc, Prod.le_def] at h₄ h₅ h₆ h₇ ⊢
          constructor <;>
          (try constructor) <;>
          (try constructor) <;>
          (try constructor) <;>
          (try simp_all [f]) <;>
          (try nlinarith)
        have h₄ : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
          exact Set.finite_Icc _ _
        exact Set.Finite.subset h₄ h₃
      have h₃ : ∃ (i j : ℕ), i < j ∧ f i = f j := by
        by_contra! h₄
        have h₅ : Function.Injective f := by
          intro i j h₆
          by_cases h₇ : i = j
          · exact h₇
          · have h₈ : i < j ∨ j < i := by omega
            cases h₈ with
            | inl h₈ =>
              have h₉ := h₄ i j h₈
              simp_all
            | inr h₈ =>
              have h₉ := h₄ j i h₈
              simp_all
        have h₆ : Set.Infinite (Set.range f) := Set.infinite_range_of_injective h₅
        exact Set.not_infinite.mpr h₂ h₆
      obtain ⟨i, j, h₄, h₅⟩ := h₃
      refine' ⟨i, j, h₄, _⟩
      simp [f] at h₅ ⊢
      <;>
      (try simp_all [Prod.ext_iff]) <;>
      (try omega) <;>
      (try aesop)
    exact h₁
  have h_periodic : ∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n := by
    obtain ⟨i, j, hij, h_eq⟩ := h_main
    have h₁ : ∀ m : ℕ, u (i + m) = u (j + m) := by
      intro m
      have h₂ : ∀ m : ℕ, u (i + m) = u (j + m) := by
        intro m
        induction m using Nat.strong_induction_on with
        | h m ih =>
          match m with
          | 0 =>
            have h₃ := h_eq.1
            simp at h₃ ⊢
            <;> simp_all [add_assoc]
          | 1 =>
            have h₃ := h_eq.2.1
            simp at h₃ ⊢
            <;> simp_all [add_assoc]
            <;> ring_nf at *
            <;> omega
          | 2 =>
            have h₃ := h_eq.2.2.1
            simp at h₃ ⊢
            <;> simp_all [add_assoc]
            <;> ring_nf at *
            <;> omega
          | 3 =>
            have h₃ := h_eq.2.2.2
            simp at h₃ ⊢
            <;> simp_all [add_assoc]
            <;> ring_nf at *
            <;> omega
          | m + 4 =>
            have h₃ : i + (m + 4) ≥ 4 := by
              have h₄ : i ≥ 0 := by linarith
              omega
            have h₄ : u (i + (m + 4)) = ((u (i + (m + 4) - 1) + u (i + (m + 4) - 2) + u (i + (m + 4) - 3) * u (i + (m + 4) - 4)) : ℝ) / (u (i + (m + 4) - 1) * u (i + (m + 4) - 2) + u (i + (m + 4) - 3) + u (i + (m + 4) - 4)) := by
              have h₅ := hu (i + (m + 4)) (by omega)
              have h₆ := h₅.1
              norm_cast at h₆ ⊢
              <;> simp_all [add_assoc]
              <;> ring_nf at *
              <;> norm_num at *
              <;> linarith
            have h₅ : u (j + (m + 4)) = ((u (j + (m + 4) - 1) + u (j + (m + 4) - 2) + u (j + (m + 4) - 3) * u (j + (m + 4) - 4)) : ℝ) / (u (j + (m + 4) - 1) * u (j + (m + 4) - 2) + u (j + (m + 4) - 3) + u (j + (m + 4) - 4)) := by
              have h₆ := hu (j + (m + 4)) (by
                have h₇ : j ≥ i + 1 := by omega
                omega
              )
              have h₇ := h₆.1
              norm_cast at h₇ ⊢
              <;> simp_all [add_assoc]
              <;> ring_nf at *
              <;> norm_num at *
              <;> linarith
            have h₆ : (i + (m + 4) - 1 : ℕ) = i + (m + 3) := by
              omega
            have h₇ : (i + (m + 4) - 2 : ℕ) = i + (m + 2) := by
              omega
            have h₈ : (i + (m + 4) - 3 : ℕ) = i + (m + 1) := by
              omega
            have h₉ : (i + (m + 4) - 4 : ℕ) = i + m := by
              omega
            have h₁₀ : (j + (m + 4) - 1 : ℕ) = j + (m + 3) := by
              omega
            have h₁₁ : (j + (m + 4) - 2 : ℕ) = j + (m + 2) := by
              omega
            have h₁₂ : (j + (m + 4) - 3 : ℕ) = j + (m + 1) := by
              omega
            have h₁₃ : (j + (m + 4) - 4 : ℕ) = j + m := by
              omega
            have h₁₄ : u (i + (m + 3)) = u (j + (m + 3)) := by
              have h₁₅ := ih (m + 3) (by omega)
              simp [add_assoc] at h₁₅ ⊢
              <;> omega
            have h₁₅ : u (i + (m + 2)) = u (j + (m + 2)) := by
              have h₁₆ := ih (m + 2) (by omega)
              simp [add_assoc] at h₁₆ ⊢
              <;> omega
            have h₁₆ : u (i + (m + 1)) = u (j + (m + 1)) := by
              have h₁₇ := ih (m + 1) (by omega)
              simp [add_assoc] at h₁₇ ⊢
              <;> omega
            have h₁₇ : u (i + m) = u (j + m) := by
              have h₁₈ := ih m (by omega)
              simp [add_assoc] at h₁₈ ⊢
              <;> omega
            have h₁₈ : (u (i + (m + 4)) : ℝ) = (u (j + (m + 4)) : ℝ) := by
              rw [h₄, h₅]
              simp [h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃] at *
              norm_cast at *
              <;>
              (try simp_all [h₁₄, h₁₅, h₁₆, h₁₇]) <;>
              (try ring_nf at *) <;>
              (try field_simp at *) <;>
              (try norm_cast at *) <;>
              (try linarith)
            norm_cast at h₁₈ ⊢
            <;>
            (try simp_all) <;>
            (try linarith)
      exact h₂ m
    have h₂ : ∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n := by
      use i, (j - i)
      have h₃ : j - i > 0 := by
        omega
      constructor
      · exact h₃
      · intro n hn
        have h₄ : u (n + (j - i)) = u n := by
          have h₅ : u (i + (n - i)) = u (j + (n - i)) := by
            have h₆ := h₁ (n - i)
            simp [add_assoc] at h₆ ⊢
            <;> omega
          have h₆ : i + (n - i) = n := by
            omega
          have h₇ : j + (n - i) = n + (j - i) := by
            omega
          rw [h₆] at h₅
          rw [h₇] at h₅
          linarith
        exact h₄
    exact h₂
  exact h_periodic

#check _root_.putnam_1964_a4
#print axioms _root_.putnam_1964_a4
