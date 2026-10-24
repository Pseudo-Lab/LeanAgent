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

open Set Function Filter Topology


#repair_guard "by\n  have h_subset_or_compl : ∀ (A : Set S), A ∈ P ∨ Aᶜ ∈ P := by\n    intro A\n    by_contra! h\n    have h₁ : A ∉ P := h.1\n    have h₂ : Aᶜ ∉ P := h.2\n\n    have h₃ : ∃ (U : Set S), U ∈ P ∧ A ∩ U = ∅ := by\n      have h₄ : ¬(A ∉ P ∧ ∀ (U : Set S), U ∈ P → A ∩ U ≠ ∅) := by\n        intro h₅\n        have h₆ : ∃ (T : Set S), T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅) := by\n          refine' ⟨A, _⟩\n          constructor\n          · exact h₅.1\n          · intro U hU\n            have h₇ := h₅.2 U hU\n            have h₈ : A ∩ U ≠ ∅ := h₇\n            have h₉ : A ∩ U = U ∩ A := by\n              ext x\n              simp [Set.mem_inter_iff]\n              <;> tauto\n            have h₁₀ : U ∩ A ≠ ∅ := by\n              intro h₁₁\n              apply h₈\n              simp_all [Set.ext_iff]\n              <;> aesop\n            simpa [Set.inter_comm] using h₁₀\n        exact hPS h₆\n      by_cases h₅ : A ∉ P\n      · have h₆ : ¬(∀ (U : Set S), U ∈ P → A ∩ U ≠ ∅) := by\n          intro h₇\n          exact h₄ ⟨h₅, h₇⟩\n        push_neg at h₆\n        obtain ⟨U, hU, h₈⟩ := h₆\n        refine' ⟨U, hU, _⟩\n        have h₉ : A ∩ U = ∅ := by\n          by_contra h₁₀\n          have h₁₁ : A ∩ U ≠ ∅ := h₁₀\n          simp_all [Set.ext_iff]\n          <;> aesop\n        exact h₉\n      · exfalso\n        simp_all\n\n    have h₄ : ∃ (V : Set S), V ∈ P ∧ Aᶜ ∩ V = ∅ := by\n      have h₅ : ¬(Aᶜ ∉ P ∧ ∀ (U : Set S), U ∈ P → Aᶜ ∩ U ≠ ∅) := by\n        intro h₆\n        have h₇ : ∃ (T : Set S), T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅) := by\n          refine' ⟨Aᶜ, _⟩\n          constructor\n          · exact h₆.1\n          · intro U hU\n            have h₈ := h₆.2 U hU\n            have h₉ : Aᶜ ∩ U ≠ ∅ := h₈\n            have h₁₀ : Aᶜ ∩ U = U ∩ Aᶜ := by\n              ext x\n              simp [Set.mem_inter_iff]\n              <;> tauto\n            have h₁₁ : U ∩ Aᶜ ≠ ∅ := by\n              intro h₁₂\n              apply h₉\n              simp_all [Set.ext_iff]\n              <;> aesop\n            simpa [Set.inter_comm] using h₁₁\n        exact hPS h₇\n      by_cases h₆ : Aᶜ ∉ P\n      · have h₇ : ¬(∀ (U : Set S), U ∈ P → Aᶜ ∩ U ≠ ∅) := by\n          intro h₈\n          exact h₅ ⟨h₆, h₈⟩\n        push_neg at h₇\n        obtain ⟨V, hV, h₈⟩ := h₇\n        refine' ⟨V, hV, _⟩\n        have h₉ : Aᶜ ∩ V = ∅ := by\n          by_contra h₁₀\n          have h₁₁ : Aᶜ ∩ V ≠ ∅ := h₁₀\n          simp_all [Set.ext_iff]\n          <;> aesop\n        exact h₉\n      · exfalso\n        simp_all\n\n    obtain ⟨U, hU, hU'⟩ := h₃\n    obtain ⟨V, hV, hV'⟩ := h₄\n\n    have h₅ : U ⊆ Aᶜ := by\n      intro x hx\n      by_contra h₆\n      have h₇ : x ∈ A := by simp_all [Set.mem_compl_iff]\n      have h₈ : x ∈ A ∩ U := Set.mem_inter h₇ hx\n      rw [hU'] at h₈\n      simp at h₈\n      <;> aesop\n    have h₆ : V ⊆ A := by\n      intro x hx\n      by_contra h₇\n      have h₈ : x ∈ Aᶜ := by simp_all [Set.mem_compl_iff]\n      have h₉ : x ∈ Aᶜ ∩ V := Set.mem_inter h₈ hx\n      rw [hV'] at h₉\n      simp at h₉\n      <;> aesop\n\n    have h₇ : U ∩ V = ∅ := by\n      apply Set.eq_empty_of_forall_not_mem\n      intro x hx\n      have h₈ : x ∈ U := Set.mem_of_mem_inter_left hx\n      have h₉ : x ∈ V := Set.mem_of_mem_inter_right hx\n      have h₁₀ : x ∈ Aᶜ := h₅ h₈\n      have h₁₁ : x ∈ A := h₆ h₉\n      simp_all [Set.mem_compl_iff]\n      <;> aesop\n\n    have h₈ : U ∩ V ≠ ∅ := hPP U hU V hV\n    simp_all [Set.ext_iff]\n    <;> aesop\n\n  have h_not_both : ∀ (A : Set S), A ∈ P → Aᶜ ∉ P := by\n    intro A hA\n    by_contra h\n    have h₁ : Aᶜ ∈ P := h\n    have h₂ : A ∩ Aᶜ = ∅ := by\n      ext x\n      simp [Set.mem_inter_iff]\n      <;> tauto\n    have h₃ : A ∩ Aᶜ ≠ ∅ := hPP A hA Aᶜ h₁\n    rw [h₂] at h₃\n    contradiction\n\n  have h_card : P.card = 2 ^ (Fintype.card S - 1) := by\n    classical\n\n    let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \\ P\n\n    have h₁ : P.card = Q.card := by\n      have h₂ : ∀ (A : Set S), A ∈ P → Aᶜ ∈ Q := by\n        intro A hA\n        have h₃ : Aᶜ ∈ (Finset.univ : Finset (Set S)) := Finset.mem_univ _\n        have h₄ : Aᶜ ∉ P := h_not_both A hA\n        simp only [Q, Finset.mem_sdiff] at *\n        tauto\n      have h₃ : ∀ (A : Set S), A ∈ Q → Aᶜ ∈ P := by\n        intro A hA\n        have h₄ : A ∈ (Finset.univ : Finset (Set S)) := by\n          simp only [Q, Finset.mem_sdiff] at hA\n          tauto\n        have h₅ : A ∉ P := by\n          simp only [Q, Finset.mem_sdiff] at hA\n          tauto\n        have h₆ : A ∈ (Finset.univ : Finset (Set S)) := by tauto\n        have h₇ : A ∈ P ∨ Aᶜ ∈ P := h_subset_or_compl A\n        cases h₇ with\n        | inl h₈ =>\n          exfalso\n          tauto\n        | inr h₈ =>\n          exact h₈\n\n      have h₄ : P.card = Q.card := by\n        have h₅ : P.card = Q.card := by\n          have h₆ : ∀ (A : Set S), A ∈ P → Aᶜ ∈ Q := h₂\n          have h₇ : ∀ (A : Set S), A ∈ Q → Aᶜ ∈ P := h₃\n          have h₈ : P.card = Q.card := by\n            apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)\n            <;> simp_all [Set.ext_iff]\n            <;>\n            (try\n              {\n                aesop\n              })\n            <;>\n            (try\n              {\n                tauto\n              })\n            <;>\n            (try\n              {\n                intros\n                <;>\n                simp_all [Set.ext_iff]\n                <;>\n                tauto\n              })\n            <;>\n            (try\n              {\n                intros\n                <;>\n                simp_all [Set.ext_iff]\n                <;>\n                tauto\n              })\n          exact h₈\n        exact h₅\n      exact h₄\n\n    have h₂ : P.card + Q.card = 2 ^ Fintype.card S := by\n      have h₃ : P.card + Q.card = (Finset.univ : Finset (Set S)).card := by\n        have h₄ : Disjoint P Q := by\n          rw [Finset.disjoint_left]\n          intro A hA hA'\n          simp only [Q, Finset.mem_sdiff] at hA'\n          tauto\n        have h₅ : P ∪ Q = (Finset.univ : Finset (Set S)) := by\n          apply Finset.ext\n          intro A\n          simp only [Q, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]\n          <;>\n          by_cases h₆ : A ∈ P <;> simp_all [h_subset_or_compl]\n          <;>\n          (try tauto)\n          <;>\n          (try\n            {\n              have h₇ := h_subset_or_compl A\n              cases h₇ with\n              | inl h₈ => tauto\n              | inr h₈ =>\n                have h₉ : Aᶜ ∈ P := h₈\n                have h₁₀ : A ∈ P ∨ Aᶜ ∈ P := by tauto\n                tauto\n            })\n        have h₆ : P.card + Q.card = (P ∪ Q).card := by\n          rw [← Finset.card_union_add_card_inter P Q]\n          have h₇ : P ∩ Q = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h₄\n          rw [h₇]\n          simp\n        rw [h₅] at h₆\n        exact h₆\n      have h₄ : (Finset.univ : Finset (Set S)).card = 2 ^ Fintype.card S := by\n        simp [Fintype.card_fun]\n        <;>\n        simp_all [Fintype.card_fun]\n        <;>\n        ring_nf\n        <;>\n        simp_all [Fintype.card_fun]\n        <;>\n        norm_num\n        <;>\n        aesop\n      linarith\n\n    have h₃ : P.card * 2 = 2 ^ Fintype.card S := by\n      have h₄ : P.card + Q.card = 2 ^ Fintype.card S := h₂\n      have h₅ : P.card = Q.card := h₁\n      linarith\n\n    have h₄ : Fintype.card S ≥ 1 := by\n      have h₅ : Nonempty S := inferInstance\n      have h₆ : 0 < Fintype.card S := by\n        apply Fintype.card_pos_iff.mpr\n        exact ⟨Classical.choice h₅⟩\n      omega\n    have h₅ : P.card = 2 ^ (Fintype.card S - 1) := by\n      have h₆ : P.card * 2 = 2 ^ Fintype.card S := h₃\n      have h₇ : Fintype.card S ≥ 1 := h₄\n      have h₈ : 2 ^ (Fintype.card S - 1) * 2 = 2 ^ Fintype.card S := by\n        have h₉ : Fintype.card S - 1 + 1 = Fintype.card S := by\n          have h₁₀ : Fintype.card S ≥ 1 := h₄\n          omega\n        calc\n          2 ^ (Fintype.card S - 1) * 2 = 2 ^ (Fintype.card S - 1) * 2 ^ 1 := by norm_num\n          _ = 2 ^ ((Fintype.card S - 1) + 1) := by\n            rw [← pow_add]\n          _ = 2 ^ Fintype.card S := by\n            rw [h₉]\n            <;> simp [add_comm]\n      have h₉ : P.card = 2 ^ (Fintype.card S - 1) := by\n        have h₁₀ : P.card * 2 = 2 ^ Fintype.card S := h₃\n        have h₁₁ : 2 ^ (Fintype.card S - 1) * 2 = 2 ^ Fintype.card S := h₈\n        have h₁₂ : P.card = 2 ^ (Fintype.card S - 1) := by\n          nlinarith\n        exact h₁₂\n      exact h₉\n    exact h₅\n\n  exact h_card"
theorem putnam_1964_b2
(S : Type*) [Fintype S] [Nonempty S]
(P : Finset (Set S))
(hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅)
(hPS : ¬∃ T : Set S, T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅))
: (P.card = 2 ^ (Fintype.card S - 1)) := by
  sorry

