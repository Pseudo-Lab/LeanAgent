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


#repair_measure
theorem putnam_1964_b2
(S : Type*) [Fintype S] [Nonempty S]
(P : Finset (Set S))
(hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅)
(hPS : ¬∃ T : Set S, T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅))
: (P.card = 2 ^ (Fintype.card S - 1)) := by
  have h_no_empty : ∀ (T : Set S), T ∈ P → T.Nonempty := by
    intro T hT
    have h₁ : T ∩ T ≠ ∅ := hPP T hT T hT
    have h₂ : T ∩ T = T := by simp [Set.ext_iff]
    rw [h₂] at h₁
    by_contra h₃
    apply h₁
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    exact h₃ ⟨x, hx⟩
  
  have h_subset_or_compl : ∀ (A : Set S), A ∈ P ∨ Aᶜ ∈ P := by
    intro A
    by_contra! h
    have h₁ : A ∉ P := h.1
    have h₂ : Aᶜ ∉ P := h.2
    
    have h₃ : ∃ (U : Set S), U ∈ P ∧ A ∩ U = ∅ := by
      have h₄ : ¬(A ∉ P ∧ ∀ (U : Set S), U ∈ P → A ∩ U ≠ ∅) := by
        intro h₅
        have h₆ : ∃ (T : Set S), T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅) := by
          refine' ⟨A, _⟩
          constructor
          · exact h₅.1
          · intro U hU
            have h₇ := h₅.2 U hU
            have h₈ : A ∩ U ≠ ∅ := h₇
            have h₉ : A ∩ U = U ∩ A := by
              ext x
              simp [Set.mem_inter_iff]
              <;> tauto
            have h₁₀ : U ∩ A ≠ ∅ := by
              intro h₁₁
              apply h₈
              simp_all [Set.ext_iff]
              <;> aesop
            simpa [Set.inter_comm] using h₁₀
        exact hPS h₆
      by_cases h₅ : A ∉ P
      · have h₆ : ¬(∀ (U : Set S), U ∈ P → A ∩ U ≠ ∅) := by
          intro h₇
          exact h₄ ⟨h₅, h₇⟩
        push_neg at h₆
        obtain ⟨U, hU, h₈⟩ := h₆
        refine' ⟨U, hU, _⟩
        have h₉ : A ∩ U = ∅ := by
          by_contra h₁₀
          have h₁₁ : A ∩ U ≠ ∅ := h₁₀
          simp_all [Set.ext_iff]
          <;> aesop
        exact h₉
      · exfalso
        simp_all
    
    have h₄ : ∃ (V : Set S), V ∈ P ∧ Aᶜ ∩ V = ∅ := by
      have h₅ : ¬(Aᶜ ∉ P ∧ ∀ (U : Set S), U ∈ P → Aᶜ ∩ U ≠ ∅) := by
        intro h₆
        have h₇ : ∃ (T : Set S), T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅) := by
          refine' ⟨Aᶜ, _⟩
          constructor
          · exact h₆.1
          · intro U hU
            have h₈ := h₆.2 U hU
            have h₉ : Aᶜ ∩ U ≠ ∅ := h₈
            have h₁₀ : Aᶜ ∩ U = U ∩ Aᶜ := by
              ext x
              simp [Set.mem_inter_iff]
              <;> tauto
            have h₁₁ : U ∩ Aᶜ ≠ ∅ := by
              intro h₁₂
              apply h₉
              simp_all [Set.ext_iff]
              <;> aesop
            simpa [Set.inter_comm] using h₁₁
        exact hPS h₇
      by_cases h₆ : Aᶜ ∉ P
      · have h₇ : ¬(∀ (U : Set S), U ∈ P → Aᶜ ∩ U ≠ ∅) := by
          intro h₈
          exact h₅ ⟨h₆, h₈⟩
        push_neg at h₇
        obtain ⟨V, hV, h₈⟩ := h₇
        refine' ⟨V, hV, _⟩
        have h₉ : Aᶜ ∩ V = ∅ := by
          by_contra h₁₀
          have h₁₁ : Aᶜ ∩ V ≠ ∅ := h₁₀
          simp_all [Set.ext_iff]
          <;> aesop
        exact h₉
      · exfalso
        simp_all
    
    obtain ⟨U, hU, hU'⟩ := h₃
    obtain ⟨V, hV, hV'⟩ := h₄
    
    have h₅ : U ⊆ Aᶜ := by
      intro x hx
      by_contra h₆
      have h₇ : x ∈ A := by simp_all [Set.mem_compl_iff]
      have h₈ : x ∈ A ∩ U := Set.mem_inter h₇ hx
      rw [hU'] at h₈
      simp at h₈
      <;> aesop
    have h₆ : V ⊆ A := by
      intro x hx
      by_contra h₇
      have h₈ : x ∈ Aᶜ := by simp_all [Set.mem_compl_iff]
      have h₉ : x ∈ Aᶜ ∩ V := Set.mem_inter h₈ hx
      rw [hV'] at h₉
      simp at h₉
      <;> aesop
    
    have h₇ : U ∩ V = ∅ := by
      apply Set.eq_empty_of_forall_not_mem
      intro x hx
      have h₈ : x ∈ U := Set.mem_of_mem_inter_left hx
      have h₉ : x ∈ V := Set.mem_of_mem_inter_right hx
      have h₁₀ : x ∈ Aᶜ := h₅ h₈
      have h₁₁ : x ∈ A := h₆ h₉
      simp_all [Set.mem_compl_iff]
      <;> aesop
    
    have h₈ : U ∩ V ≠ ∅ := hPP U hU V hV
    simp_all [Set.ext_iff]
    <;> aesop
  
  have h_not_both : ∀ (A : Set S), A ∈ P → Aᶜ ∉ P := by
    intro A hA
    by_contra h
    have h₁ : Aᶜ ∈ P := h
    have h₂ : A ∩ Aᶜ = ∅ := by
      ext x
      simp [Set.mem_inter_iff]
      <;> tauto
    have h₃ : A ∩ Aᶜ ≠ ∅ := hPP A hA Aᶜ h₁
    rw [h₂] at h₃
    contradiction
  
  have h_card : P.card = 2 ^ (Fintype.card S - 1) := by
    classical
    
    let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \ P
    
    have h₁ : P.card = Q.card := by
      
      have h₂ : ∀ (A : Set S), A ∈ P → Aᶜ ∈ Q := by
        intro A hA
        have h₃ : Aᶜ ∈ (Finset.univ : Finset (Set S)) := Finset.mem_univ _
        have h₄ : Aᶜ ∉ P := h_not_both A hA
        simp only [Q, Finset.mem_sdiff] at *
        tauto
      have h₃ : ∀ (A : Set S), A ∈ Q → Aᶜ ∈ P := by
        intro A hA
        have h₄ : A ∈ (Finset.univ : Finset (Set S)) := by
          simp only [Q, Finset.mem_sdiff] at hA
          tauto
        have h₅ : A ∉ P := by
          simp only [Q, Finset.mem_sdiff] at hA
          tauto
        have h₆ : A ∈ (Finset.univ : Finset (Set S)) := by tauto
        have h₇ : A ∈ P ∨ Aᶜ ∈ P := h_subset_or_compl A
        cases h₇ with
        | inl h₈ =>
          exfalso
          tauto
        | inr h₈ =>
          exact h₈
      
      have h₄ : P.card = Q.card := by
        
        have h₅ : P.card = Q.card := by
          
          have h₆ : ∀ (A : Set S), A ∈ P → Aᶜ ∈ Q := h₂
          have h₇ : ∀ (A : Set S), A ∈ Q → Aᶜ ∈ P := h₃
          
          have h₈ : P.card = Q.card := by
            
            apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
            <;> simp_all [Set.ext_iff]
            <;>
            (try
              {
                aesop
              })
            <;>
            (try
              {
                tauto
              })
            <;>
            (try
              {
                intros
                <;>
                simp_all [Set.ext_iff]
                <;>
                tauto
              })
            <;>
            (try
              {
                intros
                <;>
                simp_all [Set.ext_iff]
                <;>
                tauto
              })
          exact h₈
        exact h₅
      exact h₄
    
    have h₂ : P.card + Q.card = 2 ^ Fintype.card S := by
      have h₃ : P.card + Q.card = (Finset.univ : Finset (Set S)).card := by
        have h₄ : Disjoint P Q := by
          rw [Finset.disjoint_left]
          intro A hA hA'
          simp only [Q, Finset.mem_sdiff] at hA'
          tauto
        have h₅ : P ∪ Q = (Finset.univ : Finset (Set S)) := by
          apply Finset.ext
          intro A
          simp only [Q, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
          <;>
          by_cases h₆ : A ∈ P <;> simp_all [h_subset_or_compl]
          <;>
          (try tauto)
          <;>
          (try
            {
              have h₇ := h_subset_or_compl A
              cases h₇ with
              | inl h₈ => tauto
              | inr h₈ =>
                have h₉ : Aᶜ ∈ P := h₈
                have h₁₀ : A ∈ P ∨ Aᶜ ∈ P := by tauto
                tauto
            })
        have h₆ : P.card + Q.card = (P ∪ Q).card := by
          rw [← Finset.card_union_add_card_inter P Q]
          have h₇ : P ∩ Q = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h₄
          rw [h₇]
          simp
        rw [h₅] at h₆
        exact h₆
      have h₄ : (Finset.univ : Finset (Set S)).card = 2 ^ Fintype.card S := by
        simp [Fintype.card_fun]
        <;>
        simp_all [Fintype.card_fun]
        <;>
        ring_nf
        <;>
        simp_all [Fintype.card_fun]
        <;>
        norm_num
        <;>
        aesop
      linarith
    
    have h₃ : P.card * 2 = 2 ^ Fintype.card S := by
      have h₄ : P.card + Q.card = 2 ^ Fintype.card S := h₂
      have h₅ : P.card = Q.card := h₁
      linarith
    
    have h₄ : Fintype.card S ≥ 1 := by
      have h₅ : Nonempty S := inferInstance
      have h₆ : 0 < Fintype.card S := by
        apply Fintype.card_pos_iff.mpr
        exact ⟨Classical.choice h₅⟩
      omega
    have h₅ : P.card = 2 ^ (Fintype.card S - 1) := by
      have h₆ : P.card * 2 = 2 ^ Fintype.card S := h₃
      have h₇ : Fintype.card S ≥ 1 := h₄
      have h₈ : 2 ^ (Fintype.card S - 1) * 2 = 2 ^ Fintype.card S := by
        have h₉ : Fintype.card S - 1 + 1 = Fintype.card S := by
          have h₁₀ : Fintype.card S ≥ 1 := h₄
          omega
        calc
          2 ^ (Fintype.card S - 1) * 2 = 2 ^ (Fintype.card S - 1) * 2 ^ 1 := by norm_num
          _ = 2 ^ ((Fintype.card S - 1) + 1) := by
            rw [← pow_add]
          _ = 2 ^ Fintype.card S := by
            rw [h₉]
            <;> simp [add_comm]
      have h₉ : P.card = 2 ^ (Fintype.card S - 1) := by
        have h₁₀ : P.card * 2 = 2 ^ Fintype.card S := h₃
        have h₁₁ : 2 ^ (Fintype.card S - 1) * 2 = 2 ^ Fintype.card S := h₈
        have h₁₂ : P.card = 2 ^ (Fintype.card S - 1) := by
          nlinarith
        exact h₁₂
      exact h₉
    exact h₅
  
  exact h_card

#check _root_.putnam_1964_b2
#print axioms _root_.putnam_1964_b2
