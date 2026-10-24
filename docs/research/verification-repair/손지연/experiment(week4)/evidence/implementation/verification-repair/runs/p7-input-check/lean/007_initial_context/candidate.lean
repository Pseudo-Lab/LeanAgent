/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Typing

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file proves type safety.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

public section

namespace Cslib

variable {Var : Type*} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open Context List Env.Wf Term Ty

variable {t : Term Var}

set_option linter.tacticAnalysis.verifyGrindOnly false in
lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  generalize eq : [] = Γ at der
  -- Retain the typing derivation to recover local closure after induction.
  have wholeTyped : Typing Γ t τ := der
  induction der <;> subst eq
  case var => grind
  case app t₁ _ _ t₂ leftTyped rightTyped ihLeft ihRight =>
    right
    trace_state
    rcases ihLeft rfl wholeTyped with leftValue | ⟨t₁', step⟩
    · rcases ihRight rfl rightTyped with rightValue | ⟨t₂', step⟩
      · obtain ⟨σ, body, rfl⟩ := leftTyped.canonical_form_abs leftValue
        exact ⟨_, Red.abs leftValue.lc rightValue⟩
      · exact ⟨_, Red.appᵣ leftValue step⟩
    · exact ⟨_, Red.appₗ rightTyped.wf.2.1 step⟩
  case tapp σ' typed _ ih =>
    right
    rcases ih rfl typed with value | ⟨t', step⟩
    · obtain ⟨_, body, eq⟩ := typed.canonical_form_tabs value
      exists body ^ᵗᵞ σ'
      grind
    · exists .tapp t' σ'
      grind
  case let' t₁ σ t₂ τ L typed _ ih _ =>
    right
    rcases ih rfl typed with value | ⟨t₁', step⟩
    · exists t₂ ^ᵗᵗ t₁
      grind
    · exists t₁'.let' t₂
      grind
  case inl typed _ ih | inr typed _ ih =>
    -- The two injections share the same value and congruence-step argument.
    rcases ih rfl typed with value | ⟨t', step⟩
    · left
      constructor
      exact value
    · right
      exact ⟨_, by constructor; exact step⟩
  case case t₁ _ _ t₂ _ t₃ _ typed _ _ ih _ _ =>
    right
    rcases ih rfl typed with value | ⟨t₁', step⟩
    · obtain ⟨t₁, side⟩ := typed.canonical_form_sum value
      cases side <;> [exists t₂ ^ᵗᵗ t₁; exists t₃ ^ᵗᵗ t₁] <;> grind
    · exists t₁'.case t₂ t₃
      grind
  case sub => grind
  case abs | tabs =>
    left
    constructor
    exact wholeTyped.wf.2.1

#check Typing.progress
#print axioms Typing.progress

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
