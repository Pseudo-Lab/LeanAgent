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


#repair_measure
theorem putnam_1995_a3
(relation : (Fin 9 → ℤ) → (Fin 9 → ℤ) → Prop)
(digits_to_num : (Fin 9 → ℤ) → ℤ)
(hdigits_to_num : digits_to_num = fun dig => ∑ i : Fin 9, (dig i) * 10^i.1)
(hrelation : ∀ d e : (Fin 9 → ℤ), relation d e ↔ (∀ i : Fin 9, d i < 10 ∧ d i ≥ 0 ∧ e i < 10 ∧ e i ≥ 0) ∧ (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j))))
: ∀ d e f : (Fin 9 → ℤ), ((relation d e) ∧ (relation e f)) → (∀ i : Fin 9, 7 ∣ d i - f i) := by 
  have h_main : ∀ (d e f : (Fin 9 → ℤ)), ((relation d e) ∧ (relation e f)) → (∀ i : Fin 9, 7 ∣ d i - f i) := by
    intro d e f h
    have h₁ : relation d e := h.1
    have h₂ : relation e f := h.2
    have h₃ : ∀ (i : Fin 9), 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j)) := by
      have h₄ : (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j))) := (hrelation d e).mp h₁ |>.2
      exact h₄
    have h₄ : ∀ (i : Fin 9), 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then f j else e j)) := by
      have h₅ : (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then f j else e j))) := (hrelation e f).mp h₂ |>.2
      exact h₅
    
    have h₅ : ∀ (i : Fin 9), 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := by
      intro i
      have h₆ : 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j)) := h₃ i
      have h₇ : (digits_to_num (fun j : Fin 9 => if j = i then e j else d j)) = digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
        calc
          (digits_to_num (fun j : Fin 9 => if j = i then e j else d j)) = ∑ j : Fin 9, (if j = i then e j else d j) * (10 : ℤ) ^ (j : ℕ) := by
            simp [hdigits_to_num]
            <;>
            rfl
          _ = ∑ j : Fin 9, (if j = i then e j else d j) * (10 : ℤ) ^ (j : ℕ) := rfl
          _ = (∑ j : Fin 9, d j * (10 : ℤ) ^ (j : ℕ)) + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
            calc
              (∑ j : Fin 9, (if j = i then e j else d j) * (10 : ℤ) ^ (j : ℕ)) = ∑ j : Fin 9, (d j * (10 : ℤ) ^ (j : ℕ) + (if j = i then (e j - d j) else 0) * (10 : ℤ) ^ (j : ℕ)) := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases h : j = i
                · simp [h]
                  <;> ring
                · simp [h]
                  <;> ring
              _ = (∑ j : Fin 9, d j * (10 : ℤ) ^ (j : ℕ)) + ∑ j : Fin 9, (if j = i then (e j - d j) else 0) * (10 : ℤ) ^ (j : ℕ) := by
                rw [Finset.sum_add_distrib]
              _ = (∑ j : Fin 9, d j * (10 : ℤ) ^ (j : ℕ)) + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
                have h₈ : ∑ j : Fin 9, (if j = i then (e j - d j) else 0) * (10 : ℤ) ^ (j : ℕ) = (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
                  calc
                    _ = ∑ j : Fin 9, (if j = i then (e j - d j) else 0) * (10 : ℤ) ^ (j : ℕ) := rfl
                    _ = (if i = i then (e i - d i) else 0) * (10 : ℤ) ^ (i : ℕ) := by
                      
                      simp [Finset.sum_ite_eq', Finset.mem_univ, i.is_lt]
                    _ = (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by simp
                rw [h₈]
                <;> simp [hdigits_to_num]
                <;>
                rfl
          _ = digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
            simp [hdigits_to_num]
            <;>
            rfl
      have h₈ : 7 ∣ digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
        rw [h₇] at h₆
        exact h₆
      
      have h₉ : 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := by
        
        have h₁₀ : (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d = digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by ring
        rw [h₁₀]
        exact h₈
      exact h₉
    
    have h₆ : ∀ (i : Fin 9), 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e := by
      intro i
      have h₇ : 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then f j else e j)) := h₄ i
      have h₈ : (digits_to_num (fun j : Fin 9 => if j = i then f j else e j)) = digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
        calc
          (digits_to_num (fun j : Fin 9 => if j = i then f j else e j)) = ∑ j : Fin 9, (if j = i then f j else e j) * (10 : ℤ) ^ (j : ℕ) := by
            simp [hdigits_to_num]
            <;>
            rfl
          _ = ∑ j : Fin 9, (if j = i then f j else e j) * (10 : ℤ) ^ (j : ℕ) := rfl
          _ = (∑ j : Fin 9, e j * (10 : ℤ) ^ (j : ℕ)) + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
            calc
              (∑ j : Fin 9, (if j = i then f j else e j) * (10 : ℤ) ^ (j : ℕ)) = ∑ j : Fin 9, (e j * (10 : ℤ) ^ (j : ℕ) + (if j = i then (f j - e j) else 0) * (10 : ℤ) ^ (j : ℕ)) := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases h : j = i
                · simp [h]
                  <;> ring
                · simp [h]
                  <;> ring
              _ = (∑ j : Fin 9, e j * (10 : ℤ) ^ (j : ℕ)) + ∑ j : Fin 9, (if j = i then (f j - e j) else 0) * (10 : ℤ) ^ (j : ℕ) := by
                rw [Finset.sum_add_distrib]
              _ = (∑ j : Fin 9, e j * (10 : ℤ) ^ (j : ℕ)) + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
                have h₉ : ∑ j : Fin 9, (if j = i then (f j - e j) else 0) * (10 : ℤ) ^ (j : ℕ) = (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
                  calc
                    _ = ∑ j : Fin 9, (if j = i then (f j - e j) else 0) * (10 : ℤ) ^ (j : ℕ) := rfl
                    _ = (if i = i then (f i - e i) else 0) * (10 : ℤ) ^ (i : ℕ) := by
                      
                      simp [Finset.sum_ite_eq', Finset.mem_univ, i.is_lt]
                    _ = (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by simp
                rw [h₉]
                <;> simp [hdigits_to_num]
                <;>
                rfl
          _ = digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
            simp [hdigits_to_num]
            <;>
            rfl
      have h₉ : 7 ∣ digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
        rw [h₈] at h₇
        exact h₇
      
      have h₁₀ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e := by
        
        have h₁₁ : (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e = digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by ring
        rw [h₁₁]
        exact h₉
      exact h₁₀
    
    have h₇ : 7 ∣ digits_to_num e + digits_to_num d := by
      have h₈ : digits_to_num e = digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
        calc
          digits_to_num e = ∑ i : Fin 9, e i * (10 : ℤ) ^ (i : ℕ) := by simp [hdigits_to_num]
          _ = ∑ i : Fin 9, (d i + (e i - d i)) * (10 : ℤ) ^ (i : ℕ) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = ∑ i : Fin 9, (d i * (10 : ℤ) ^ (i : ℕ) + (e i - d i) * (10 : ℤ) ^ (i : ℕ)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (∑ i : Fin 9, d i * (10 : ℤ) ^ (i : ℕ)) + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
            rw [Finset.sum_add_distrib]
          _ = digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
            simp [hdigits_to_num]
            <;>
            rfl
      have h₉ : ∀ i : Fin 9, 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := h₅
      have h₁₀ : 7 ∣ ∑ i : Fin 9, ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) := by
        apply Finset.dvd_sum
        intro i _
        exact h₉ i
      have h₁₁ : ∑ i : Fin 9, ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) = ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + 9 * digits_to_num d := by
        calc
          ∑ i : Fin 9, ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) = ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + ∑ i : Fin 9, digits_to_num d := by
            rw [Finset.sum_add_distrib]
          _ = ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + 9 * digits_to_num d := by
            simp [Finset.sum_const, Finset.card_fin]
            <;> ring
            <;> norm_num
      have h₁₂ : 7 ∣ ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + 9 * digits_to_num d := by
        rw [h₁₁] at h₁₀
        exact h₁₀
      have h₁₃ : 7 ∣ digits_to_num e + digits_to_num d := by
        have h₁₄ : digits_to_num e + digits_to_num d = 2 * digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
          linarith
        rw [h₁₄]
        have h₁₅ : 7 ∣ 2 * digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
          have h₁₆ : 7 ∣ ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + 9 * digits_to_num d := h₁₂
          have h₁₇ : 7 ∣ 2 * digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
            
            have h₁₈ : (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) + 9 * digits_to_num d) = (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 9 * digits_to_num d := by ring
            rw [h₁₈] at h₁₆
            
            
            
            
            
            
            have h₁₉ : 7 ∣ (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 2 * digits_to_num d := by
              
              
              
              have h₂₀ : 7 ∣ (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 9 * digits_to_num d := h₁₆
              have h₂₁ : 7 ∣ 7 * digits_to_num d := by
                use digits_to_num d
                <;> ring
              have h₂₂ : 7 ∣ (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 2 * digits_to_num d := by
                
                have h₂₃ : (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 2 * digits_to_num d = ((∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 9 * digits_to_num d) - 7 * digits_to_num d := by ring
                rw [h₂₃]
                exact dvd_sub h₂₀ h₂₁
              exact h₂₂
            
            have h₂₀ : 7 ∣ 2 * digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
              
              have h₂₁ : 2 * digits_to_num d + ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) = (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) + 2 * digits_to_num d := by ring
              rw [h₂₁]
              exact h₁₉
            exact h₂₀
          exact h₁₇
        exact h₁₅
      exact h₁₃
    
    have h₈ : ∀ (i : Fin 9), 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
      intro i
      have h₉ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e := h₆ i
      have h₁₀ : 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := h₅ i
      have h₁₁ : 7 ∣ digits_to_num e + digits_to_num d := h₇
      
      have h₁₂ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d := by
        
        
        have h₁₃ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e := h₆ i
        have h₁₄ : 7 ∣ digits_to_num e + digits_to_num d := h₇
        
        have h₁₅ : 7 ∣ ((f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e) - (digits_to_num e + digits_to_num d) := by
          exact dvd_sub h₁₃ h₁₄
        
        have h₁₆ : ((f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e) - (digits_to_num e + digits_to_num d) = (f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d := by
          ring
        rw [h₁₆] at h₁₅
        exact h₁₅
      
      have h₁₃ : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
        have h₁₄ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d := h₁₂
        have h₁₅ : 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := h₅ i
        
        have h₁₆ : 7 ∣ ((f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d) + ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) := by
          exact dvd_add h₁₄ h₁₅
        
        have h₁₇ : ((f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d) + ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) = (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
          ring
        rw [h₁₇] at h₁₆
        exact h₁₆
      exact h₁₃
    
    have h₉ : ∀ (i : Fin 9), 7 ∣ d i - f i := by
      intro i
      have h₁₀ : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := h₈ i
      have h₁₁ : 7 ∣ (f i - d i) := by
        
        have h₁₂ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := h₁₀
        
        have h₁₃ : (7 : ℕ).Prime := by decide
        have h₁₄ : ¬(7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by
          
          intro h
          have h₁₅ : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by
            norm_cast at h ⊢
            <;> simpa [Int.coe_nat_dvd_left] using h
          have h₁₆ : (7 : ℕ) ∣ 10 := by
            
            exact Nat.Prime.dvd_of_dvd_pow h₁₃ h₁₅
          norm_num at h₁₆
          <;> contradiction
        
        have h₁₅ : (7 : ℤ) ∣ (f i - d i) := by
          
          have h₁₆ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := h₁₂
          have h₁₇ : ¬(7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := h₁₄
          
          have h₁₈ : (7 : ℤ) ∣ (f i - d i) := by
            
            have h₁₉ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := h₁₂
            have h₂₀ : (7 : ℕ).Prime := by decide
            have h₂₁ : (7 : ℤ) ∣ (f i - d i) ∨ (7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by
              
              have h₂₂ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := h₁₂
              have h₂₃ : (7 : ℤ) ∣ (f i - d i) ∨ (7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by
                
                apply (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp
                exact h₂₂
              exact h₂₃
            cases h₂₁ with
            | inl h₂₁ =>
              exact h₂₁
            | inr h₂₁ =>
              exfalso
              exact h₁₄ h₂₁
          exact h₁₈
        exact h₁₅
      
      have h₁₂ : 7 ∣ d i - f i := by
        have h₁₃ : 7 ∣ (f i - d i) := h₁₁
        have h₁₄ : 7 ∣ -(f i - d i) := by
          exact dvd_neg.mpr h₁₃
        have h₁₅ : -(f i - d i) = d i - f i := by ring
        rw [h₁₅] at h₁₄
        exact h₁₄
      exact h₁₂
    
    intro i
    have h₁₀ : 7 ∣ d i - f i := h₉ i
    exact h₁₀
  exact h_main

#check _root_.putnam_1995_a3
#print axioms _root_.putnam_1995_a3
