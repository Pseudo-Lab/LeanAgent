/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Syntax.Congruence
public import Cslib.Languages.CCS.Semantics

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

/-! # Behavioural theory of CCS

## Main results

- `CCS.bisimilarityCongruence`: bisimilarity is a congruence in CCS.

Additionally, some standard laws of bisimilarity for CCS, including:
- `CCS.bisimilarity_par_nil`: P | 𝟎 ~ P.
- `CCS.bisimilarity_par_comm`: P | Q ~ Q | P
- `CCS.bisimilarity_choice_comm`: P + Q ~ Q + P
-/

@[expose] public section

namespace Cslib

section CCS.BehaviouralTheory

open LTS

variable {Name : Type u} {Constant : Type v} {defs : Constant → CCS.Process Name Constant → Prop}

namespace CCS

open Process Act Act.Co Context

attribute [local grind] Tr

@[local grind]
private inductive ParNil : Process Name Constant → Process Name Constant → Prop where
| parNil : ParNil (par p nil) p

/-- P | 𝟎 ~ P -/
@[simp, scoped grind .]
theorem bisimilarity_par_nil : (par p nil) ~[lts (defs := defs)] p := by
  unfold lts at *
  exists ParNil, .parNil
  intro _ _ _ _
  constructor
  case left => grind
  case right =>
    intro s2' htr
    exists par s2' nil
    grind

@[local grind]
private inductive ParComm : Process Name Constant → Process Name Constant → Prop where
| parComm : ParComm (par p q) (par q p)

/-- P | Q ~ Q | P -/
@[scoped grind .]
theorem bisimilarity_par_comm : (par p q) ~[lts (defs := defs)] (par q p) := by
  let defParComm : Process Name Constant → Process Name Constant
    | par p q => par q p
    | _ => nil
  use ParComm, ParComm.parComm
  intro _ _ _ _
  unfold lts at *
  split_ands <;> intro p _ <;> exists defParComm p <;> grind

/-- 𝟎 | P ~ P -/
@[simp, scoped grind .]
theorem bisimilarity_nil_par : (par nil p) ~[lts (defs := defs)] p :=
  calc
    (par nil p) ~[lts (defs := defs)] (par p nil) := by grind
    _ ~[lts (defs := defs)] p := by simp

@[local grind]
private inductive ParAssoc : Process Name Constant → Process Name Constant → Prop where
  | assoc : ParAssoc (par p (par q r)) (par (par p q) r)
  | id : ParAssoc p p

/-- P | (Q | R) ~ (P | Q) | R -/
theorem bisimilarity_par_assoc :
    (par p (par q r)) ~[lts (defs := defs)] (par (par p q) r) := by
  use ParAssoc, ParAssoc.assoc
  intro s1 s2 hr μ
  apply And.intro <;> cases hr
  case right.assoc =>
    intro s2' htr
    unfold lts at *
    cases htr
    case parL p q r p' htr =>
      cases htr
      case parL p q r p' _ =>
        exists p'.par (q.par r)
        grind
      case parR p q r q' _ =>
        exists p.par (q'.par r)
        grind
      case com μ p' μ' q' _ htrp htrq =>
        exists p'.par (q'.par r)
        grind
    case parR p q r r' htr =>
      exists p.par (q.par r')
      grind
    case com p q r μ p' μ' r' _ htr htr' =>
      cases htr
      case parL p' _ =>
        use p'.par (q.par r')
        grind
      case parR q' _ =>
        use p.par (q'.par r')
        grind
      case com => grind
  case left.assoc =>
    intro s2' htr
    unfold lts at *
    cases htr
    case parR htr =>
      cases htr
      case parL p q r q' _ =>
        exists (p.par q').par r
        grind
      case parR p q r r' _ =>
        exists (p.par q).par r'
        grind
      case com p q r μ q' μ' r' _ htrp htrq =>
        use (p.par q').par r'
        grind
    case parL p q r p' htr =>
      exists (p'.par q).par r
      grind
    case com p q r μ p' μ' q' _ htr htr' =>
      cases htr'
      case parL q' _ =>
        use (p'.par q').par r
        grind
      case parR r' _ =>
        use (p'.par q).par r'
        grind
      case com => grind
  all_goals grind

private inductive ChoiceNil : Process Name Constant → Process Name Constant → Prop where
  | nil : ChoiceNil (choice p nil) p
  | id : ChoiceNil p p

/-- P + 𝟎 ~ P -/
theorem bisimilarity_choice_nil : (choice p nil) ~[lts (defs := defs)] p := by
  use ChoiceNil, ChoiceNil.nil
  intro s1 s2 hr μ
  apply And.intro <;> cases hr
  case left.nil =>
    unfold lts
    grind [ChoiceNil]
  case right.nil =>
    intro s2' htr
    exists s2'
    constructor
    · apply Tr.choiceL
      assumption
    · exact ChoiceNil.id
  all_goals grind [ChoiceNil]

@[local grind]
private inductive ChoiceIdem : Process Name Constant → Process Name Constant → Prop where
  | idem : ChoiceIdem (choice p p) p
  | id : ChoiceIdem p p

/-- P + P ~ P -/
theorem bisimilarity_choice_idem :
    (choice p p) ~[lts (defs := defs)] p := by
  exists ChoiceIdem
  apply And.intro
  case left => grind
  case right =>
    intro s1 s2 hr μ
    apply And.intro <;> cases hr <;> unfold lts
    case right.idem =>
      intro s1' htr
      exists s1'
      grind
    all_goals grind

private inductive ChoiceComm : Process Name Constant → Process Name Constant → Prop where
  | choiceComm : ChoiceComm (choice p q) (choice q p)
  | bisim : (p ~[lts (defs := defs)] q) → ChoiceComm p q

open Bisimilarity in
/-- P + Q ~ Q + P -/
theorem bisimilarity_choice_comm : (choice p q) ~[lts (defs := defs)] (choice q p) := by
  exists @ChoiceComm Name Constant defs
  repeat constructor
  intro s1 s2 hr μ
  cases hr
  case choiceComm p q =>
    constructor
    case left =>
      intro s1' htr
      exists s1'
      constructor
      · unfold lts
        cases htr with grind
      · grind [HomBisimilarity.refl, ChoiceComm]
    case right =>
      intro s1' htr
      exists s1'
      constructor
      · unfold lts
        cases htr with grind
      · grind [HomBisimilarity.refl, ChoiceComm]
  case bisim h =>
    grind [IsBisimulation, ChoiceComm]

private inductive ChoiceAssoc : Process Name Constant → Process Name Constant → Prop where
  | assoc : ChoiceAssoc (choice p (choice q r)) (choice (choice p q) r)
  | id : ChoiceAssoc p p

/-- P + (Q + R) ~ (P + Q) + R -/
theorem bisimilarity_choice_assoc :
    (choice p (choice q r)) ~[lts (defs := defs)] (choice (choice p q) r) := by
  use ChoiceAssoc, ChoiceAssoc.assoc
  intro s1 s2 hr μ
  apply And.intro <;> cases hr
  case left.assoc p q r =>
    intro s htr
    refine ⟨s, ?_, ChoiceAssoc.id⟩
    cases htr
    case choiceL htr => apply Tr.choiceL; apply Tr.choiceL; assumption
    case choiceR htr =>
      cases htr
      case choiceL htr => apply Tr.choiceL; apply Tr.choiceR; assumption
      case choiceR htr => apply Tr.choiceR; assumption
  case right.assoc p q r =>
    intro s htr
    refine ⟨s, ?_, ChoiceAssoc.id⟩
    cases htr
    case choiceL htr =>
      cases htr
      case choiceL htr => apply Tr.choiceL; assumption
      case choiceR htr => apply Tr.choiceR; apply Tr.choiceL; assumption
    case choiceR htr => apply Tr.choiceR; apply Tr.choiceR; assumption
  all_goals grind [ChoiceAssoc.id]

@[local grind]
private inductive PreBisim : Process Name Constant → Process Name Constant → Prop where
| pre : (p ~[lts (defs := defs)] q) → PreBisim (pre μ p) (pre μ q)
| bisim : (p ~[lts (defs := defs)] q) → PreBisim p q

/-- P ~ Q → μ.P ~ μ.Q -/
theorem bisimilarity_congr_pre :
    (p ~[lts (defs := defs)] q) → (pre μ p) ~[lts (defs := defs)] (pre μ q) := by
  intro hpq
  exists @PreBisim _ _ defs
  constructor
  · grind
  intro s1 s2 hr μ'
  cases hr
  case pre p' q' μ hbis =>
    unfold lts
    constructor <;> intro _ _ <;> [exists q'; exists p'] <;> grind
  case bisim => grind [IsBisimulation, IsBisimulation.le_bisimilarity]

@[local grind]
private inductive ResBisim : Process Name Constant → Process Name Constant → Prop where
| res : (p ~[lts (defs := defs)] q) → ResBisim (res a p) (res a q)
-- | bisim : (p ~[lts (defs := defs)] q) → ResBisim p q

/-- P ~ Q → (ν a) P ~ (ν a) Q -/
theorem bisimilarity_congr_res :
    (p ~[lts (defs := defs)] q) → (res a p) ~[lts (defs := defs)] (res a q) := by
  intro hpq
  exists @ResBisim _ _ defs
  constructor
  · grind
  intro s1 s2 hr μ'
  cases hr
  rename_i p q a h
  constructor
  case left =>
    intro s1' htr
    cases htr with | res _ _ htr =>
    obtain ⟨q', _, bisim⟩ := h.follow_fst htr
    exists res a q'
    unfold lts at *
    #adaptation_note
    /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
    split_ands
    · grind
    · exact ResBisim.res bisim
  case right =>
    intro s2' htr
    cases htr with | res _ _ htr =>
    obtain ⟨p', _, bisim⟩ := h.follow_snd htr
    exists res a p'
    unfold lts at *
    #adaptation_note
    /-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
    split_ands
    · grind
    · exact ResBisim.res bisim

private inductive ChoiceBisim : Process Name Constant → Process Name Constant → Prop where
| choice : (p ~[lts (defs := defs)] q) → ChoiceBisim (choice p r) (choice q r)
| bisim : (p ~[lts (defs := defs)] q) → ChoiceBisim p q

#repair_measure
/-- P ~ Q → P + R ~ Q + R -/
theorem bisimilarity_congr_choice :
    (p ~[lts (defs := defs)] q) → (choice p r) ~[lts (defs := defs)] (choice q r) := by
  intro h
  use @ChoiceBisim _ _ defs, .choice h
  intro _ _ hr _
  cases hr with
  | choice h =>
    constructor <;> intro s' ht
    · cases ht with
      | choiceL ht =>
        obtain ⟨q', ht, h'⟩ := h.follow_fst ht
        exact ⟨q', .choiceL ht, .bisim h'⟩
      | choiceR ht => exact ⟨s', .choiceR ht, .bisim (.refl _)⟩
    · cases ht with
      | choiceL ht =>
        obtain ⟨p', ht, h'⟩ := h.follow_snd ht
        exact ⟨p', .choiceL ht, .bisim h'⟩
      | choiceR ht => exact ⟨s', .choiceR ht, .bisim (.refl _)⟩
  | bisim h =>
    constructor <;> intro s' ht
    · obtain ⟨q', ht, h'⟩ := h.follow_fst ht
      exact ⟨q', ht, .bisim h'⟩
    · obtain ⟨p', ht, h'⟩ := h.follow_snd ht
      exact ⟨p', ht, .bisim h'⟩

@[local grind]
private inductive ParBisim : Process Name Constant → Process Name Constant → Prop where
| par : (p ~[lts (defs := defs)] q) → ParBisim (par p r) (par q r)

/-- P ~ Q → P | R ~ Q | R -/
theorem bisimilarity_congr_par :
    (p ~[lts (defs := defs)] q) → (par p r) ~[lts (defs := defs)] (par q r) := by
  intro h
  exists @ParBisim _ _ defs
  constructor
  · grind
  intro s1 s2 r μ
  constructor
  case left =>
    intro s1' htr
    cases r
    unfold lts at *
    have : {Tr :=  Tr (defs := defs)} = lts (defs := defs) := by rfl
    case par p q r hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      cases htr
      case parL p' htr =>
        obtain ⟨q', _⟩ := hb.follow_fst hr htr
        exists par q' r
        grind
      case parR r' htr =>
        exists par q r'
        grind
      case com r' _ htrp _ =>
        obtain ⟨q', _⟩ := hb.follow_fst hr htrp
        exists par q' r'
        grind
  case right =>
    intro s2' htr
    cases r
    unfold lts at *
    have : {Tr :=  Tr (defs := defs)} = lts (defs := defs) := by rfl
    case par p _ r hbisim =>
      obtain ⟨_, hr, hb⟩ := hbisim
      cases htr
      case parL htr =>
        obtain ⟨p', _⟩ := hb.follow_snd hr htr
        exists par p' r
        grind
      case parR _ _ r' htr =>
        exists par p r'
        grind
      case com r' hco htrq htrr =>
        obtain ⟨q', _⟩ := hb.follow_snd hr htrq
        exists par q' r'
        grind

/-- Bisimilarity is a congruence in CCS. -/
theorem bisimilarity_is_congruence
    (p q : Process Name Constant) (c : Context Name Constant) (h : p ~[lts (defs := defs)] q) :
    (c.fill p) ~[lts (defs := defs)] (c.fill q) := by
  induction c with
  | parR r c _ =>
    calc
      _ ~[lts (defs := defs)] (c.fill p |>.par r)  := by grind
      _ ~[lts (defs := defs)] (c.fill q |>.par r)  := by grind [bisimilarity_congr_par]
      _ ~[lts (defs := defs)] (c.parR r |>.fill q) := by grind
  | choiceR r c _ =>
    calc
      _ ~[lts (defs := defs)] (c.fill p |>.choice r)  := by grind [bisimilarity_choice_comm]
      _ ~[lts (defs := defs)] (c.fill q |>.choice r)  := by grind [bisimilarity_congr_choice]
      _ ~[lts (defs := defs)] (c.choiceR r |>.fill q) := by grind [bisimilarity_choice_comm]
  | _ => grind [bisimilarity_congr_pre, bisimilarity_congr_par,
                bisimilarity_congr_choice, bisimilarity_congr_res]

instance : Congruence (HomBisimilarity (lts (defs := defs))) := ⟨⟩

/-- Bisimilarity is a congruence in CCS. -/
instance bisimilarityCongruence :
    LawfulCongruence (HomBisimilarity (lts (defs := defs))) where
  elim := by
    dsimp [Congruence.r]
    grind [Covariant, bisimilarity_is_congruence]

end CCS

end CCS.BehaviouralTheory

end Cslib

#check _root_.Cslib.CCS.bisimilarity_congr_choice
#print axioms _root_.Cslib.CCS.bisimilarity_congr_choice
