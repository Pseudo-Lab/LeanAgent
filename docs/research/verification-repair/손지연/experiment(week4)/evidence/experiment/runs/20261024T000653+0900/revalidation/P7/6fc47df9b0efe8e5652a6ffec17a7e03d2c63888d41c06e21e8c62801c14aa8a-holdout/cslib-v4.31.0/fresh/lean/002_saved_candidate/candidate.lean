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

/-- Any reduction step preserves typing. -/
lemma Typing.preservation (der : Typing Γ t τ) (step : t ⭢βᵛ t') : Typing Γ t' τ := by
  induction der generalizing t'
  case app Γ _ σ τ _ _ _ _ _ =>
    cases step
    case appₗ | appᵣ => grind
    case abs der _ _ =>
      have sub : Sub Γ (σ.arrow τ) (σ.arrow τ) := by grind [Sub.refl]
      have ⟨_, _, ⟨_, _⟩⟩ := der.abs_inv sub
      grind [fresh_exists <| free_union [fvTm] Var, openTm_substTm_intro, subst_tm, Sub.weaken]
  case tapp Γ _ σ τ σ' _ _ _ =>
    cases step
    case tabs der _ _ =>
      have sub : Sub Γ (σ.all τ) (σ.all τ) := by grind [Sub.refl]
      have ⟨_, _, ⟨_, _⟩⟩ := der.tabs_inv sub
      have ⟨X, mem⟩ := fresh_exists <| free_union [Ty.fv, fvTy] Var
      simp at mem
      have : Γ = (Context.mapVal (·[X:=σ']) []) ++ Γ := by grind
      rw [openTy_substTy_intro (X := X), open_subst_intro (X := X)] <;> grind [subst_ty]
    case tapp => grind
  case let' Γ _ _ _ _ L der _ ih₁ _ =>
    cases step
    case let_bind red₁ _ => apply Typing.let' L (ih₁ red₁); grind
    case let_body =>
      grind [fresh_exists <| free_union [fvTm] Var, openTm_substTm_intro, subst_tm]
  case case Γ _ σ τ _ _ _ L _ _ _ ih₁ _ _ =>
    have sub : Sub Γ (σ.sum τ) (σ.sum τ) := by grind [Sub.refl]
    have : Γ = [] ++ Γ := by rfl
    cases step
    case «case» red₁ _ _ => apply Typing.case L (ih₁ red₁) <;> grind
    case case_inl der _ _ =>
      have ⟨_, ⟨_, _⟩⟩ := der.inl_inv sub
      grind [fresh_exists <| free_union [fvTm] Var, openTm_substTm_intro, subst_tm]
    case case_inr der _ _ =>
      have ⟨_, ⟨_, _⟩⟩ := der.inr_inv sub
      grind [fresh_exists <| free_union [fvTm] Var, openTm_substTm_intro, subst_tm]
  all_goals grind [cases Red]

set_option linter.tacticAnalysis.verifyGrindOnly false in
/-- Any typable term either has a reduction step or is a value. -/
lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  generalize eq : [] = Γ at der
  have der' : Typing Γ t τ := der
  induction der <;> subst eq
  case var => grind
  case app t₁ _ _ t₂ l r il ir =>
    right
    rcases il rfl l with vl | ⟨t₁', h₁⟩
    · rcases ir rfl r with vr | ⟨t₂', h₂⟩
      · obtain ⟨_, u, hu⟩ := l.canonical_form_abs vl
        exact ⟨u ^ᵗᵗ t₂, by grind⟩
      · exact ⟨t₁.app t₂', by grind⟩
    · exact ⟨t₁'.app t₂, by grind⟩
  case tapp σ' der _ ih =>
    right
    rcases ih rfl der with v | ⟨t', h⟩
    · obtain ⟨_, u, hu⟩ := der.canonical_form_tabs v
      exact ⟨u ^ᵗᵞ σ', by grind⟩
    · exact ⟨.tapp t' σ', by grind⟩
  case let' t₁ _ t₂ _ _ der _ ih _ =>
    right
    rcases ih rfl der with v | ⟨t₁', h⟩
    · exact ⟨t₂ ^ᵗᵗ t₁, by grind⟩
    · exact ⟨t₁'.let' t₂, by grind⟩
  case inl der _ ih =>
    rcases ih rfl der with v | ⟨t', h⟩
    · grind
    · exact .inr ⟨.inl t', by grind⟩
  case inr der _ ih =>
    rcases ih rfl der with v | ⟨t', h⟩
    · grind
    · exact .inr ⟨.inr t', by grind⟩
  case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>
    right
    rcases ih rfl der with v | ⟨t₁', h⟩
    · obtain ⟨u, h | h⟩ := der.canonical_form_sum v
      · exact ⟨t₂ ^ᵗᵗ u, by grind⟩
      · exact ⟨t₃ ^ᵗᵗ u, by grind⟩
    · exact ⟨t₁'.case t₂ t₃, by grind⟩
  case sub => grind
  case abs _ _ _ L _ _ =>
    left
    constructor
    apply LC.abs L
    · grind only [→ wf, cases Term.LC]
    · grind only [→ wf]
  case tabs L _ _ =>
    left
    constructor
    apply LC.tabs L
    · grind only [→ wf, cases Term.LC]
    · grind only [→ wf]

end LambdaCalculus.LocallyNameless.Fsub

end Cslib

#check _root_.Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress
#print axioms _root_.Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress
