/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import Lean

import all Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.CmdSemanticsProps
import all Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Imperative.HasVars
import all Strata.DL.Util.Nodup
public import Strata.DL.Util.ListUtils
import all Strata.DL.Util.ListUtils
import all Strata.Languages.Core.Statement
public import Strata.Languages.Core.StatementSemantics
import all Strata.Languages.Core.StatementSemantics
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.Stmt
import Std.Tactic.BVDecide.Normalize.BitVec

public section

/-! ## Theorems related to StatementSemantics -/

namespace Core
open Imperative

theorem InitStatesEmpty :
  @InitStates P σ [] [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem UpdateStatesEmpty :
  @UpdateStates P σ [] [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem HavocVarsEmpty {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P} :
  HavocVars f σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem InitVarsEmpty :
  @InitVars P σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem TouchVarsEmpty :
  @TouchVars P σ [] σ' → σ = σ' := by
  intros H; cases H <;> simp

theorem EvalBlockEmpty' {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendFactory : ExtendFactory P}
  { ρ ρ' : Env P }
  [HasBool P] [HasBoolOps P] [HasFvars P] [HasInt P] [HasIntOps P] :
  EvalStmtsSmall P EvalCmd extendFactory ρ ([]: (List (Stmt P Cmd))) ρ' → ρ = ρ' := by
  intro H
  match H with
  | .step _ _ _ .step_stmts_nil (.refl _) => rfl

theorem EvalStatementsEmpty :
  EvalStatements π φ ρ [] ρ' → ρ = ρ' := by
  intro H
  unfold EvalStatements EvalStmtsSmall at H
  match H with
  | .step _ _ _ .step_stmts_nil (.refl _) => rfl

theorem EvalStatementsContractEmpty :
  EvalStatementsContract π φ ρ [] ρ' → ρ = ρ' := by
  intro H
  unfold EvalStatementsContract EvalStmtsSmall at H
  match H with
  | .step _ _ _ .step_stmts_nil (.refl _) => rfl

theorem UpdateStateNotDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isNotDefined σ vs →
  UpdateState P σ v e σ' →
  isNotDefined σ' vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp [isNotDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [Hsome]
    exact Hdef Hv'

theorem UpdateStatesNotDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isNotDefined σ vs →
  UpdateStates σ vs' es' σ' →
  isNotDefined σ' vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply ih
  exact UpdateStateNotDefMonotone Hdef Hup
  assumption

theorem UpdateStateNotDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isNotDefined σ' vs →
  UpdateState P σ v e σ' →
  isNotDefined σ vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp [isNotDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [← Hsome]
    exact Hdef Hv'

theorem UpdateStatesNotDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isNotDefined σ' vs →
  UpdateStates σ vs' es' σ' →
  isNotDefined σ vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply UpdateStateNotDefMonotone' (ih Hdef) Hup
  exact Hv

theorem InitStateDefined
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @InitState P σ v e σ' →
  isDefined σ' [v] := by
  intros Hup
  cases Hup with
  | init Hold Hsome Hall =>
  simp [isDefined, Option.isSome, Hsome]

theorem UpdateStateDefined
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @UpdateState P σ v e σ' →
  isDefined σ' [v] := by
  intros Hup
  cases Hup with
  | update Hold Hsome Hall =>
  simp [isDefined, Option.isSome, Hsome]

theorem UpdateStateDefined'
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @UpdateState P σ v e σ' →
  isDefined σ [v] := by
  intros Hup
  cases Hup with
  | update Hold Hsome Hall =>
  simp [isDefined, Option.isSome]
  split <;> simp_all

theorem UpdateStateDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  UpdateState P σ v e σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp [isDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp [Option.isSome]
    simp [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [Hsome]
    exact Hdef Hv'

theorem UpdateStatesDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isDefined σ vs →
  UpdateStates σ vs' es' σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply ih
  exact UpdateStateDefMonotone Hdef Hup
  assumption

theorem UpdateStateDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ' vs →
  UpdateState P σ v e σ' →
  isDefined σ vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp [isDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp [Option.isSome]
    simp [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [← Hsome]
    exact Hdef Hv'

theorem UpdateStatesDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isDefined σ' vs →
  UpdateStates σ vs' es' σ' →
  isDefined σ vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply UpdateStateDefMonotone' (ih Hdef) Hup
  exact Hv

theorem UpdateStatesDefined :
  UpdateStates σ vs es σ' →
  isDefined σ' vs := by
  intros Hhavoc
  induction vs generalizing es σ σ'
  case nil => simp [isDefined]
  case cons h t ih =>
    cases Hhavoc with
    | @update_some _ _ v σ₁ _ _ Hup Hhav =>
    apply isDefinedCons
    apply UpdateStatesDefMonotone <;> try assumption
    exact UpdateStateDefined Hhav
    apply ih <;> assumption

theorem UpdateStatesDefined' :
  UpdateStates σ vs es σ' →
  isDefined σ vs := by
  intros Hhavoc
  induction vs generalizing es σ σ'
  case nil => simp [isDefined]
  case cons h t ih =>
    cases Hhavoc with
    | update_some Hup Hups =>
    apply isDefinedCons
    exact UpdateStateDefined' Hup
    apply UpdateStatesDefMonotone'
    apply ih Hups
    exact UpdateStates.update_some Hup UpdateStates.update_none

theorem updatedStateUpdate {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v v' : P.Expr} :
  σ h = some v' →
  UpdateState P σ h v (@updatedState P σ h v) := by
  intros Hsome
  constructor <;> try simp [updatedState]
  assumption
  intros v Hneq Heq; simp_all

theorem updatedStateId {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v : P.Expr} :
  σ h = some v →
  @updatedState P σ h v = σ := by
  intros Hsome
  funext x
  simp_all [updatedState]

theorem updatedStateDefMonotone :
  isDefined σ vs →
  isDefined (updatedState σ v' e') vs := by
  intros Hdef
  induction vs
  case nil => simp [isDefined]
  case cons h t ih =>
    simp [isDefined] at *
    apply And.intro
    . simp [Option.isSome]
      split <;> simp_all
      next x heq =>
      simp [updatedState] at heq
      split at heq <;> simp_all
    . intros id Hin
      apply ih <;> simp_all

theorem updatedStatesDefMonotone
  {P : PureExpr} {σ : SemanticStore P}
  {vs : List P.Ident} {ves : List (P.Ident × P.Expr)} :
  isDefined σ vs →
  isDefined (updatedStates' σ ves) vs := by
  intros Hdef
  induction ves generalizing σ <;>
  unfold updatedStates' <;> try simp_all
  case cons h t ih =>
    simp [isDefined]
    intros v Hin
    apply ih
    exact updatedStateDefMonotone Hdef
    assumption

  theorem updatedStatesDefined :
  ks.length = vs.length →
  isDefined (updatedStates σ ks vs) ks := by
  intros Hlen k Hin
  induction ks generalizing σ vs <;> simp_all
  case cons h t ih =>
  simp [updatedStates] at *
  cases vs <;> simp at Hlen
  case cons h' t' =>
  cases Hin with
  | inl Hin =>
    simp [updatedStates']
    have Hdef : isDefined (updatedStates' (updatedState σ h h') (t.zip t')) [h] := by
      apply updatedStatesDefMonotone
      simp [isDefined, updatedState]
    simp_all [isDefined]
  | inr Hin =>
    apply ih <;> assumption

theorem updatedStatesUpdate {P : PureExpr}
  {σ : SemanticStore P} {hs : List P.Ident} {vs : List P.Expr} :
  hs.length = vs.length →
  isDefined σ hs →
  UpdateStates σ hs vs (updatedStates σ hs vs) := by
  intros Hlen Hdef
  induction hs generalizing vs σ
  case nil =>
    simp_all
    have Hemp : vs = [] := by
      exact List.length_eq_zero_iff.mp (id (Eq.symm Hlen))
    simp [Hemp, updatedStates]
    exact UpdateStates.update_none
  case cons h t ih =>
    induction vs <;> simp_all
    case cons h' t' =>
    simp [isDefined] at Hdef
    have Hlkup := Hdef.1
    simp [Option.isSome] at Hlkup
    split at Hlkup <;> simp_all
    next x val heq =>
    apply UpdateStates.update_some (updatedStateUpdate heq)
    exact ih rfl (updatedStateDefMonotone Hdef)

theorem updatedStateInit {P : PureExpr}
  {σ : SemanticStore P} {h : P.Ident} {v : P.Expr} :
  σ h = none →
  InitState P σ h v (@updatedState P σ h v) := by
  intros Hsome
  constructor <;> try simp [updatedState]
  assumption
  intros v Hneq Heq; simp_all

theorem updatedStatesInit {P : PureExpr}
  {σ : SemanticStore P} {hs : List P.Ident} {vs : List P.Expr} :
  hs.length = vs.length →
  isNotDefined σ hs →
  hs.Nodup →
  InitStates σ hs vs (updatedStates σ hs vs) := by
  intros Hlen Hdef Hnd
  induction hs generalizing vs σ
  case nil =>
    simp_all
    have Hemp : vs = [] := by
      exact List.length_eq_zero_iff.mp (id (Eq.symm Hlen))
    simp [Hemp, updatedStates]
    exact InitStates.init_none
  case cons h t ih =>
    induction vs <;> simp_all
    case cons h' t' =>
    simp [isNotDefined] at Hdef
    have Hlkup := Hdef.1
    simp at Hlkup
    apply InitStates.init_some (updatedStateInit Hlkup)
    apply ih rfl
    simp [isNotDefined, updatedState]
    intros v Hin
    simp_all
    exact ne_of_mem_of_not_mem Hin Hnd.1

/-- use the zipped version to avoid needing to prove length equivalent -/
theorem updatedStates'App :
  updatedStates' σ (a ++ b) =
  updatedStates' (updatedStates' σ a) b := by
  induction a generalizing σ
  case nil =>
    simp [updatedStates']
  case cons h t ih =>
    simp [updatedStates']
    rw [ih]

theorem InitStatesInitVars :
  InitStates σ hs vs σ' →
  InitVars σ hs σ' := by
  intros Hinit
  induction Hinit
  case init_none => exact InitVars.init_none
  case init_some h t ih => exact InitVars.init_some h ih

theorem InitStatesInits :
  InitStates σ hs vs σ' →
  Inits σ σ' := by
  intros Hinit
  constructor
  exact InitStatesInitVars Hinit

theorem InitStatesNotDefined :
  InitStates σ hs vs σ' → isNotDefined σ hs := by
  intros Hinit
  induction Hinit <;> simp [isNotDefined]
  case init_some x v σ' xs vs σ'' Hinit Hinits ih =>
    simp [isNotDefined] at *
    cases Hinit with
    | init Hnone Hsome Heq =>
    refine ⟨Hnone, ?_⟩
    intros x' Hin
    by_cases Heqx : x = x' <;> simp_all
    specialize Heq x' Heqx
    specialize ih x' Hin
    simp_all

theorem InitStatesNodup :
  InitStates σ hs vs σ' → hs.Nodup := by
  intros Hinit
  induction Hinit <;> simp_all
  case init_some x v σ' xs vs σ'' Hinit Hinits ih =>
  apply Not.intro
  intros Hin
  cases Hinit with
  | init Hnone Hsome Heq =>
    have Hnd := InitStatesNotDefined Hinits
    specialize Hnd x Hin
    simp_all

theorem InitStateInjective :
  InitState P σ k1 k2 σ' →
  InitState P σ k1 k2 σ'' →
  σ' = σ'' := by
  intros Hinit1 Hinit2
  cases Hinit1
  case init Hnone1 Heq1 Hsome1 =>
  cases Hinit2
  case init Hnone2 Heq2 Hsome2 =>
  funext x
  by_cases H : k1 = x
  . simp_all
  . rw [Heq1, Heq2] <;> simp_all

theorem InitStatesInjective :
  InitStates σ k1 k2 σ' →
  InitStates σ k1 k2 σ'' →
  σ' = σ'' := by
  intros Hinit1 Hinit2
  induction Hinit1 generalizing σ''
  case init_none =>
    have Heq := InitStatesEmpty Hinit2
    simp_all
  case init_some Hinit Hinits ih =>
    cases Hinit2 with
    | init_some Hinit2 Hinits2 =>
    apply ih
    have Hinj := InitStateInjective Hinit Hinit2
    simp_all

theorem ReadValuesInjective :
  ReadValues σ ks vs →
  ReadValues σ ks vs' →
  vs = vs' := by
  intros Hrd1 Hrd2
  induction Hrd1 generalizing vs'
  case read_none =>
    cases Hrd2
    rfl
  case read_some Hrd Hrds ih =>
    cases Hrd2 with
    | read_some Hrd2 Hrds2 =>
    congr
    . simp_all
    . apply ih
      simp_all

theorem InitStateUpdated :
    InitState P σ' k v σ'' →
    σ'' = updatedState σ' k v := by
  intros Hinit
  cases Hinit with
  | init Hnone Hsome Heq =>
  funext x
  simp [updatedState]
  by_cases Hxk : x = k <;> simp_all
  rw [Heq]
  exact fun a => Hxk (Eq.symm a)

theorem InitStatesUpdated :
    InitStates σ' ks vs σ'' →
    σ'' = updatedStates σ' ks vs := by
  intros Hinit
  induction Hinit
  case init_none =>
    simp [updatedStates, updatedStates']
  case init_some Hinit Hinits ih =>
    simp [ih]
    simp [updatedStates, updatedStates']
    have Heq := InitStateUpdated Hinit
    simp [Heq]

theorem UpdateStateUpdated :
    UpdateState P σ' k v σ'' →
    σ'' = updatedState σ' k v := by
  intros Hinit
  cases Hinit with
  | update Hnone Hsome Heq =>
  funext x
  simp [updatedState]
  by_cases Hxk : x = k <;> simp_all
  rw [Heq]
  exact fun a => Hxk (Eq.symm a)

theorem UpdateStatesUpdated :
    UpdateStates σ' ks vs σ'' →
    σ'' = updatedStates σ' ks vs := by
  intros Hinit
  induction Hinit
  case update_none =>
    simp [updatedStates, updatedStates']
  case update_some Hinit Hinits ih =>
    simp [ih]
    simp [updatedStates, updatedStates']
    have Heq := UpdateStateUpdated Hinit
    simp [Heq]

theorem InitStatesApp' :
  InitStates σ (k1 ++ k2) (v1 ++ v2) σ' →
  k1.length = v1.length →
  k2.length = v2.length →
  ∃ σ₁,
  σ₁ = updatedStates σ k1 v1 ∧
  InitStates σ k1 v1 σ₁ ∧
  InitStates σ₁ k2 v2 σ' := by
  intros Hinit Hlen1 Hlen2
  exists (updatedStates σ k1 v1)
  refine ⟨rfl, ?_⟩
  have H1 : InitStates σ k1 v1 (updatedStates σ k1 v1) := by
    apply updatedStatesInit Hlen1
    . have Hndef := InitStatesNotDefined Hinit
      simp [isNotDefined] at *
      simp_all
    . have Hndup := InitStatesNodup Hinit
      refine List.Sublist.nodup ?_ Hndup
      exact List.sublist_append_left k1 k2
  refine ⟨H1, ?_⟩
  generalize Hup : updatedStates σ k1 v1 = σ₁ at *
  induction H1 <;> simp_all
  case init_some σ₂ Hinit' Hinits ih =>
  apply ih
  . cases Hinit with
    | init_some Hinit Hinits =>
      simp [InitStateInjective Hinit Hinit'] at *
      assumption
  . simp [InitStateUpdated Hinit']
    exact Hup

theorem ReadValuesApp :
  ReadValues σ k1 v1 →
  ReadValues σ k2 v2 →
  ReadValues σ (k1 ++ k2) (v1 ++ v2) := by
  intros Hrd1 Hrd2
  induction Hrd1 <;> simp_all
  case read_some Hsome Hrd Hrds =>
  constructor <;> assumption

theorem ReadValuesAppKeys' :
  ReadValues σ (k1 ++ k2) vs →
  exists v1 v2,
  v1 ++ v2 = vs ∧
  ReadValues σ k1 v1 ∧
  ReadValues σ k2 v2 := by
  intros Hrd
  induction vs generalizing k1 k2
  case nil =>
    exists [],[]
    generalize Hk12 : k1 ++ k2 = k12 at Hrd
    cases Hrd
    simp_all
    constructor
  case cons vh vt vih =>
    cases k1
    case nil =>
      exists [],vh :: vt
      simp_all
      constructor
    case cons kh kt =>
      cases Hrd with
      | read_some Hsome Hrd =>
        specialize vih Hrd
        cases vih with
        | intro v1' vih =>
        cases vih with
        | intro v2 vih =>
        exists vh::v1',v2
        simp_all
        constructor <;> simp_all

theorem ReadValuesLength :
  ReadValues σ ks vs →
  ks.length = vs.length := by
  intros Hrd
  induction Hrd <;> simp_all

theorem EvalExpressionsLength :
  EvalExpressions fac σ ks vs →
  ks.length = vs.length := by
  intros Hrd
  induction Hrd <;> simp_all

theorem InitStatesLength :
  InitStates σ ks vs σ' →
  ks.length = vs.length := by
  intros Hinit
  induction Hinit <;> simp_all

theorem UpdateStatesLength {P : PureExpr}
  {σ σ' : Imperative.SemanticStore P}
  {ks : List P.Ident}
  {vs : List P.Expr}
  :
  UpdateStates (P:=P) σ ks vs σ' →
  List.length ks = List.length vs := by
  intros Hup
  induction Hup <;> simp_all

theorem InitStateReadValuesMonotone {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr} {e : P.Expr} {v : P.Ident} :
  ReadValues σ ks vs →
  InitState P σ v e σ' →
  ReadValues σ' ks vs := by
  intros Hdef Heval
  cases Heval with
  | init Hold HH Hsome =>
  induction Hdef
  case read_none => constructor
  case read_some xs vs' x v' Hsome' Hrd Hrds =>
  constructor <;> simp_all
  rw [Hsome] <;> try simp_all
  apply Not.intro
  intros Heq
  simp_all

theorem InitStatesReadValuesMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr}
  {es' : List P.Expr} {vs' : List P.Ident} :
  ReadValues σ ks vs →
  InitStates σ vs' es' σ' →
  ReadValues σ' ks vs := by
  intros Hdef Heval
  induction Heval with
  | init_none => assumption
  | init_some Hinit Hinits ih =>
    apply ih
    apply InitStateReadValuesMonotone <;> assumption

theorem UpdateStateReadValuesMonotone {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr} {e : P.Expr} {v : P.Ident} :
  ¬ v ∈ ks →
  ReadValues σ ks vs →
  UpdateState P σ v e σ' →
  ReadValues σ' ks vs := by
  intros Hnin Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  induction Hdef
  case read_none => constructor
  case read_some xs vs' x v' Hsome' Hrd Hrds =>
  constructor <;> simp_all

theorem UpdateStatesReadValuesMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr}
  {es' : List P.Expr} {vs' : List P.Ident} :
  (ks ++ vs').Nodup →
  ReadValues σ ks vs →
  UpdateStates σ vs' es' σ' →
  ReadValues σ' ks vs := by
  intros Hnd Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hinit Hinits ih =>
    have Hnd' := nodup_middle Hnd
    simp_all
    apply ih
    apply UpdateStateReadValuesMonotone _ Hdef Hinit <;> try assumption
    simp_all

theorem InitStateReadValues :
  InitState P σ v e σ' →
  ReadValues σ' [v] [e] := by
  intros Hinit
  cases Hinit with
  | init Hold HH Hsome =>
  constructor
  . assumption
  . constructor

theorem UpdateStateReadValues :
  UpdateState P σ v e σ' →
  ReadValues σ' [v] [e] := by
  intros Hinit
  cases Hinit with
  | update Hold HH Hsome =>
  constructor
  . assumption
  . constructor

theorem InitStatesReadValues :
  InitStates σ vs es σ' →
  ReadValues σ' vs es := by
  intros Hinit
  induction Hinit
  case init_none =>
    constructor
  case init_some x v σ₁ x' v' σ'' Hinit Hinits ih =>
    constructor <;> try assumption
    have Hrd : ReadValues σ'' [x] [v] := by
      apply InitStatesReadValuesMonotone (σ:=σ₁)
      apply InitStateReadValues <;> assumption
      assumption
    cases Hrd
    assumption

theorem UpdateStatesReadValues :
  vs.Nodup →
  UpdateStates σ vs es σ' →
  ReadValues σ' vs es := by
  intros Hnd Hinit
  induction Hinit
  case update_none =>
    constructor
  case update_some x v σ₁ x' v' σ'' Hupdate Hupdates ih =>
    constructor <;> try assumption
    have Hrd : ReadValues σ'' [x] [v] := by
      apply UpdateStatesReadValuesMonotone (σ:=σ₁)
      exact Hnd
      apply UpdateStateReadValues <;> assumption
      assumption
    cases Hrd
    assumption
    apply ih
    simp_all

theorem InitVarsInitStates : InitVars σ vars σ' →
  ∃ modvals, InitStates σ vars modvals σ' := by
  intros Hinit
  induction Hinit
  case init_none =>
    refine ⟨[], InitStates.init_none⟩
  case init_some σ x v σ₁ xs σ'' Hup Hhav ih =>
    cases ih with
    | intro vs Hups =>
    refine ⟨v::vs,?_⟩
    constructor <;> assumption

theorem InitVarsReadValuesMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {ks vs' : List P.Ident} {vs : List P.Expr} :
  ReadValues σ ks vs →
  InitVars σ vs' σ' →
  ReadValues σ' ks vs := by
  intros Hdef Hinit
  have Hinit' := InitVarsInitStates Hinit
  cases Hinit' with
  | intro es' Hinit' =>
  exact InitStatesReadValuesMonotone Hdef Hinit'

theorem updatedStateComm
  {P : PureExpr} {σ : SemanticStore P}
  {k k' : P.Ident} {v v' : P.Expr} :
  k ≠ k' →
  updatedState (updatedState σ k v) k' v' =
  updatedState (updatedState σ k' v') k v := by
  intros Hne
  funext x
  unfold updatedState
  by_cases Hxk' : x = k' <;> simp [Hxk']
  intros Heq
  by_cases Hxk : x = k <;> simp_all

theorem updatedStateComm'
  {P : PureExpr} {σ : SemanticStore P}
  {k : P.Ident} {v : P.Expr}
  {kvs : List (P.Ident × P.Expr)} :
  ¬ k ∈ kvs.unzip.1 →
  (updatedState (updatedStates' σ kvs) k v) =
  (updatedStates' (updatedState σ k v) kvs) := by
  intros Hnd
  induction kvs generalizing σ <;> simp [updatedStates']
  case cons h t ih =>
  rw [ih]
  rw [updatedStateComm]
  simp_all; exact fun a => Hnd.1 (Eq.symm a)
  simp_all

theorem updatedStatesComm
  {P : PureExpr} {σ : SemanticStore P}
  {kvs kvs' : List (P.Ident × P.Expr)} :
  kvs.unzip.1.Disjoint kvs'.unzip.1 →
  updatedStates' (updatedStates' σ kvs) kvs' =
  updatedStates' (updatedStates' σ kvs') kvs := by
  intros Hnd
  induction kvs generalizing kvs' σ <;> simp [updatedStates']
  case cons h t ih =>
  induction kvs' generalizing σ h <;> simp [updatedStates']
  case cons h' t' ih' =>
    rw [← ih']
    rw [updatedStateComm]
    rw [updatedStateComm']
    . simp at Hnd
      have Hnd' := List.Disjoint.symm Hnd
      apply List.Disjoint_cons_head
      apply List.Disjoint.mono_right _ Hnd'
      simp_all
    . intros Hin
      simp_all [List.Disjoint]
    . simp at *
      refine List.Disjoint.mono_right ?_ Hnd
      simp_all

theorem UpdateStateSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  v ≠ k' →
  σ k' = some v' →
  UpdateState P σ v e σ' →
  σ' k' = some v' := by
  intros Hne Hdef Heval
  have Hrd : ReadValues σ [k'] [v'] := by
    cases Heval with
    | update Hold HH Hsome =>
    constructor <;> simp_all
    constructor
  have Hrd2 : ReadValues σ' [k'] [v'] := by
    apply UpdateStateReadValuesMonotone ?_ Hrd Heval
    simp_all
  cases Hrd2
  assumption

theorem UpdateStatesSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  ¬ k' ∈ ks' →
  σ k' = some v' →
  UpdateStates σ ks' vs' σ' →
  σ' k' = some v' := by
  intros Hnin Hsome Hinit
  induction Hinit <;> try simp_all
  next Hinit Hinits ih =>
  apply ih
  apply UpdateStateSomeMonotone ?_ Hsome Hinit
  exact fun a => Hnin.1 (Eq.symm a)

theorem InitStateSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  σ k' = some v' →
  InitState P σ v e σ' →
  σ' k' = some v' := by
  intros Hdef Heval
  have Hrd : ReadValues σ [k'] [v'] := by
    cases Heval with
    | init Hold HH Hsome =>
    constructor <;> simp_all
    constructor
  have Hrd2 : ReadValues σ' [k'] [v'] :=
    InitStateReadValuesMonotone Hrd Heval
  cases Hrd2
  assumption

theorem InitStateSomeMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  k' ≠ v →
  σ' k' = some v' →
  InitState P σ v e σ' →
  σ k' = some v' := by
  intros Hne Hdef Heval
  have Hrd : ReadValues σ [k'] [v'] := by
    cases Heval with
    | init Hold HH Hsome =>
    constructor <;> simp_all
    rw [← Hsome]
    assumption
    exact fun a => Hne (Eq.symm a)
    constructor
  have Hrd2 : ReadValues σ' [k'] [v'] :=
    InitStateReadValuesMonotone Hrd Heval
  cases Hrd
  assumption

theorem InitStatesSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  σ k' = some v' →
  InitStates σ ks' vs' σ' →
  σ' k' = some v' := by
  intros Hsome Hinit
  induction Hinit <;> try simp_all
  next Hinit Hinits ih =>
  apply ih
  apply InitStateSomeMonotone Hsome Hinit

theorem InitStatesSomeMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  ¬ k' ∈ ks' →
  σ' k' = some v' →
  InitStates σ ks' vs' σ' →
  σ k' = some v' := by
  intros Hnin Hsome Hinit
  induction Hinit
  case init_none => simp_all
  case init_some Hinit Hinits ih =>
  apply InitStateSomeMonotone' ?_ ?_ Hinit
  . simp_all
  . apply ih <;> simp_all


elab "#arena_count " cmd:command : command => do
  let start ← IO.getNumHeartbeats
  Lean.Elab.Command.elabCommand (← `(command| set_option Elab.async false in $cmd))
  let finish ← IO.getNumHeartbeats
  Lean.logInfo m!"ARENA_HEARTBEATS_RAW={finish - start}"

#arena_count
theorem InitsUpdatesComm
  {P : PureExpr} {σ σ' σ'' : SemanticStore P}
  {ks ks' : List P.Ident} {vs vs' : List P.Expr} :
  UpdateStates σ ks vs σ' →
  InitStates σ' ks' vs' σ'' →
  ∃ σ₁,
    σ₁ = (updatedStates σ ks' vs') ∧
    InitStates σ ks' vs' σ₁ ∧
    UpdateStates σ₁ ks vs σ'' := by
  intros Hup Hinit
  refine ⟨updatedStates σ ks' vs', ?_⟩
  have Hk : (isDefined σ' ks) := UpdateStatesDefined Hup
  have Hlen1 := InitStatesLength Hinit
  have Hlen2 := UpdateStatesLength Hup
  induction Hup generalizing σ''
  case update_none =>
    simp_all
    apply And.intro
    refine updatedStatesInit Hlen1 ?_ ?_
    exact InitStatesNotDefined Hinit
    exact InitStatesNodup Hinit
    simp [InitStatesUpdated Hinit]
    constructor
  case update_some σ x v σ₀ xs vs σ₁ Hup Hups ih =>
    refine ⟨rfl, ?_, ?_⟩
    . apply updatedStatesInit Hlen1
      apply UpdateStateNotDefMonotone' ?_ Hup
      apply UpdateStatesNotDefMonotone' ?_ Hups
      exact InitStatesNotDefined Hinit
      exact InitStatesNodup Hinit
    . apply UpdateStates.update_some (σ':=updatedStates σ₀ ks' vs')
      . simp [UpdateStateUpdated Hup, updatedStates]
        rw [← updatedStateComm']
        . have Hdef := UpdateStateDefined' Hup
          simp [isDefined, Option.isSome] at Hdef
          split at Hdef <;> simp_all
          next val heq =>
          apply updatedStateUpdate (v':=val)
          apply InitStatesSomeMonotone heq
          apply updatedStatesInit
          . simp_all
          . apply UpdateStateNotDefMonotone' ?_ Hup
            apply UpdateStatesNotDefMonotone' ?_ Hups
            apply InitStatesNotDefined Hinit
          . exact InitStatesNodup Hinit
        . rw [List.unzip_zip] <;> simp_all
          have Hnd := InitStatesNotDefined Hinit
          simp [isNotDefined, isDefined] at *
          apply Not.intro
          intros Hin
          specialize Hnd _ Hin
          simp_all
      . apply (ih Hinit ?_ ?_).2.2
        . simp [isDefined] at * <;> simp_all
        . simp_all
#exit
