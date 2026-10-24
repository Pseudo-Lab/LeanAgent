/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Languages.CombinatoryLogic.Defs
public import Cslib.Foundations.Relation.Confluence

/-!
# SKI reduction is confluent

This file proves the **Church-Rosser** theorem for the SKI calculus, that is, if `a ↠ b` and
`a ↠ c`, `b ↠ d` and `c ↠ d` for some term `d`. More strongly (though equivalently), we show
that the relation of having a common reduct is transitive — in the above situation, `a` and `b`,
and `a` and `c` have common reducts, so the result implies the same of `b` and `c`. Note that
`MJoin Red` is symmetric (trivially) and reflexive (since `↠` is), so we in fact show that
`MJoin Red` is an equivalence.

Our proof
follows the method of Tait and Martin-Löf for the lambda calculus, as presented for instance in
Chapter 4 of Peter Selinger's notes:
<https://www.mscs.dal.ca/~selinger/papers/papers/lambdanotes.pdf>.

## Main definitions

- `ParallelReduction` : a relation `⭢ₚ` on terms such that `⭢ ⊆ ⭢ₚ ⊆ ↠`, allowing simultaneous
reduction on the head and tail of a term.

## Main results

- `parallelReduction_diamond` : parallel reduction satisfies the diamond property, that is, it is
confluent in a single step.
- `mJoin_red_equivalence` : by a general result, the diamond property for `⭢ₚ` implies the same
for its reflexive-transitive closure. This closure is exactly `↠`, which implies the
**Church-Rosser** theorem as sketched above.
-/

@[expose] public section

namespace Cslib

namespace SKI

open Red MRed Relation

/-- A reduction step allowing simultaneous reduction of disjoint redexes -/
@[reduction_sys "ₚ"]
inductive ParallelReduction : SKI → SKI → Prop
  /-- Parallel reduction is reflexive, -/
  | refl (a : SKI) : ParallelReduction a a
  /-- Contains `Red`, -/
  | red_I (a : SKI) : ParallelReduction (I ⬝ a) a
  | red_K (a b : SKI) : ParallelReduction (K ⬝ a ⬝ b) a
  | red_S (a b c : SKI) : ParallelReduction (S ⬝ a ⬝ b ⬝ c) (a ⬝ c ⬝ (b ⬝ c))
  /-- and allows simultaneous reduction of disjoint redexes. -/
  | par ⦃a a' b b' : SKI⦄ :
      ParallelReduction a a' → ParallelReduction b b' → ParallelReduction (a ⬝ b) (a' ⬝ b')

/-- The inclusion `(· ⭢ₚ ·) ≤ (· ↠ ·)`. -/
theorem ParallelReduction.le_reflTransGen_red :
    (· ⭢ₚ ·) ≤ (· ↠ ·) := by
  intro a a' h
  cases h
  case refl => exact Relation.ReflTransGen.refl
  case par a a' b b' ha hb =>
    apply parallel_mRed
    · exact ha.le_reflTransGen_red
    · exact hb.le_reflTransGen_red
  case red_I => exact Relation.ReflTransGen.single (Red.red_I a')
  case red_K b => exact Relation.ReflTransGen.single (Red.red_K a' b)
  case red_S a b c => exact Relation.ReflTransGen.single (Red.red_S a b c)

/-- The inclusion `(· ⭢ ·) ≤ (· ⭢ₚ ·)`. -/
theorem Red.le_parallelReduction :
    (· ⭢ ·) ≤ (· ⭢ₚ ·) := by
  intro a a' h
  cases h
  case red_S => apply ParallelReduction.red_S
  case red_K => apply ParallelReduction.red_K
  case red_I => apply ParallelReduction.red_I
  case red_head a a' b h =>
    apply ParallelReduction.par
    · exact h.le_parallelReduction
    · exact ParallelReduction.refl b
  case red_tail a b b' h =>
    apply ParallelReduction.par
    · exact ParallelReduction.refl a
    · exact h.le_parallelReduction

/-- The relations `⭢` and `⭢ₚ` have the same reflexive-transitive closure. -/
theorem reflTransGen_parallelReduction_mRed :
    ReflTransGen ParallelReduction = ReflTransGen Red := by
  apply le_antisymm
  · exact reflTransGen_le_of_le ParallelReduction.le_reflTransGen_red
  · exact ReflTransGen.mono Red.le_parallelReduction

/-!
Irreducibility for the (partially applied) primitive combinators.

TODO: possibly these should be proven more generally (in another file) for `↠`.
-/

lemma I_irreducible (a : SKI) (h : I ⭢ₚ a) : a = I := by
  cases h
  rfl

lemma K_irreducible (a : SKI) (h : K ⭢ₚ a) : a = K := by
  cases h
  rfl

lemma Ka_irreducible (a c : SKI) (h : (K ⬝ a) ⭢ₚ c) : ∃ a', a ⭢ₚ a' ∧ c = K ⬝ a' := by
  cases h
  case refl => use a, .refl a
  case par b a' h h' => rw [K_irreducible b h]; use a'

lemma S_irreducible (a : SKI) (h : S ⭢ₚ a) : a = S := by
  cases h
  rfl

lemma Sa_irreducible (a c : SKI) (h : (S ⬝ a) ⭢ₚ c) : ∃ a', a ⭢ₚ a' ∧ c = S ⬝ a' := by
  cases h
  case refl =>
    exact ⟨a, ParallelReduction.refl a, rfl⟩
  case par b a' h h' => rw [S_irreducible b h]; use a'

lemma Sab_irreducible (a b c : SKI) (h : (S ⬝ a ⬝ b) ⭢ₚ c) :
    ∃ a' b', a ⭢ₚ a' ∧ b ⭢ₚ b' ∧ c = S ⬝ a' ⬝ b' := by
  cases h
  case refl => use a, b, .refl a, .refl b
  case par c b' hc hb =>
    let ⟨d, hd⟩ := Sa_irreducible a c hc
    rw [hd.2]
    use d, b', hd.1

/--
The key result: the Church-Rosser property holds for `⭢ₚ`. The proof is a lengthy case analysis
on the reductions `a ⭢ₚ a₁` and `a ⭢ₚ a₂`, but is entirely mechanical.
-/
theorem parallelReduction_diamond : Diamond ParallelReduction := by
  intro a b c hab hac
  induction hab generalizing c with
  case refl a =>
    exact ⟨c, hac, ParallelReduction.refl c⟩
  case red_I a =>
    cases hac with
    | refl =>
        exact ⟨a, ParallelReduction.refl a, ParallelReduction.red_I a⟩
    | red_I =>
        exact ⟨a, ParallelReduction.refl a, ParallelReduction.refl a⟩
    | par a' b' hI ha =>
        rw [I_irreducible a' hI]
        exact ⟨b', ha, ParallelReduction.red_I b'⟩
  case red_K a b =>
    cases hac with
    | refl =>
        exact ⟨a, ParallelReduction.refl a, ParallelReduction.red_K a b⟩
    | red_K =>
        exact ⟨a, ParallelReduction.refl a, ParallelReduction.refl a⟩
    | par c' b' hKa hb =>
        obtain ⟨a', ha, hKa'⟩ := Ka_irreducible a c' hKa
        rw [hKa']
        exact ⟨a', ha, ParallelReduction.red_K a' b'⟩
  case red_S a b c =>
    cases hac with
    | refl =>
        exact ⟨a ⬝ c ⬝ (b ⬝ c), ParallelReduction.refl _,
          ParallelReduction.red_S a b c⟩
    | red_S =>
        exact ⟨a ⬝ c ⬝ (b ⬝ c), ParallelReduction.refl _,
          ParallelReduction.refl _⟩
    | par ab' c' hSab hc =>
        obtain ⟨a', b', ha, hb, hSab'⟩ := Sab_irreducible a b ab' hSab
        rw [hSab']
        exact ⟨a' ⬝ c' ⬝ (b' ⬝ c'),
          ParallelReduction.par (ParallelReduction.par ha hc)
            (ParallelReduction.par hb hc),
          ParallelReduction.red_S a' b' c'⟩
  case par a a' b b' ha hb iha ihb =>
    cases hac with
    | refl =>
        exact ⟨a' ⬝ b', ParallelReduction.refl _, ParallelReduction.par ha hb⟩
    | red_I =>
        rw [I_irreducible a' ha]
        exact ⟨b', ParallelReduction.red_I b', hb⟩
    | red_K =>
        obtain ⟨x, hx, ha'⟩ := Ka_irreducible _ a' ha
        rw [ha']
        exact ⟨x, ParallelReduction.red_K x b', hx⟩
    | red_S =>
        obtain ⟨x, y, hx, hy, ha'⟩ := Sab_irreducible _ _ a' ha
        rw [ha']
        exact ⟨x ⬝ b' ⬝ (y ⬝ b'), ParallelReduction.red_S x y b',
          ParallelReduction.par (ParallelReduction.par hx hb)
            (ParallelReduction.par hy hb)⟩
    | par c c' hc hc' =>
        obtain ⟨d, had, hcd⟩ := iha hc
        obtain ⟨d', hbd, hc'd⟩ := ihb hc'
        exact ⟨d ⬝ d', ParallelReduction.par had hbd,
          ParallelReduction.par hcd hc'd⟩

theorem join_parallelReduction_equivalence :
    Equivalence (MJoin ParallelReduction) :=
  Confluent.equivalence_join_reflTransGen <| Diamond.toConfluent parallelReduction_diamond

/-- The **Church-Rosser** theorem in its general form. -/
theorem mJoin_red_equivalence : Equivalence (MJoin Red) := by
  rw [MJoin, ←reflTransGen_parallelReduction_mRed]
  exact join_parallelReduction_equivalence

/-- The **Church-Rosser** theorem in the form it is usually stated. -/
theorem MRed.diamond : Confluent Red := by
  intro a b c hab hac
  apply mJoin_red_equivalence.trans (y := a)
  · exact mJoin_red_equivalence.symm (MJoin.single hab)
  · exact MJoin.single hac

end SKI

end Cslib
