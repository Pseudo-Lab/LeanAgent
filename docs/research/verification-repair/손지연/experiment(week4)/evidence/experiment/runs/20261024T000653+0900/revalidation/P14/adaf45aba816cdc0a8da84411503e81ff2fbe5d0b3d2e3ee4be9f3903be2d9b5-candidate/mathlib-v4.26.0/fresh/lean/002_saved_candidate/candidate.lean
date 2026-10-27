import Mathlib
import Aesop

set_option maxHeartbeats 0

open Set Function Filter Topology


theorem putnam_1964_b2
(S : Type*) [Fintype S] [Nonempty S]
(P : Finset (Set S))
(hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅)
(hPS : ¬∃ T : Set S, T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅))
: (P.card = 2 ^ (Fintype.card S - 1)) := by
  classical
  have hcomp (T : Set S) : Tᶜ ∈ P ↔ T ∉ P := by
    constructor
    · intro hTc hT
      exact (hPP T hT Tᶜ hTc) (by simp)
    · intro hT
      by_contra hTc
      have hbad : ¬∀ U ∈ P, T ∩ U ≠ ∅ := by
        intro h
        exact hPS ⟨T, hT, h⟩
      push_neg at hbad
      obtain ⟨U, hU, hTU⟩ := hbad
      apply hPS
      refine ⟨Tᶜ, hTc, ?_⟩
      intro V hV
      have hUV := hPP U hU V hV
      intro hTcV
      apply hUV
      apply Set.Subset.antisymm
      · rintro x ⟨hxU, hxV⟩
        by_cases hxT : x ∈ T
        · have hx : x ∈ T ∩ U := ⟨hxT, hxU⟩
          rw [hTU] at hx
          exact hx
        · have hxTc : x ∈ Tᶜ := hxT
          have hx : x ∈ Tᶜ ∩ V := ⟨hxTc, hxV⟩
          rw [hTcV] at hx
          exact hx
      · exact Set.empty_subset _
  let e : {T : Set S // T ∈ P} ≃
      {T : Set S // T ∈ ((Finset.univ : Finset (Set S)) \ P)} :=
    { toFun := fun T => ⟨T.1ᶜ, by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        intro hTc
        exact ((hcomp T.1).mp hTc) T.2⟩
      invFun := fun T => ⟨T.1ᶜ, by
        have hT : T.1 ∉ P := by
          simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and] using T.2
        exact (hcomp T.1).mpr hT⟩
      left_inv := by
        intro T
        apply Subtype.ext
        simp
      right_inv := by
        intro T
        apply Subtype.ext
        simp }
  have hcards : P.card = ((Finset.univ : Finset (Set S)) \ P).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  have hsdiff : ((Finset.univ : Finset (Set S)) \ P).card =
      (Finset.univ : Finset (Set S)).card - P.card := by
    exact Finset.card_sdiff (Finset.subset_univ P)
  have huniv : (Finset.univ : Finset (Set S)).card =
      2 ^ Fintype.card S := by
    rw [Finset.card_univ]
    change Fintype.card (S → Prop) = 2 ^ Fintype.card S
    simp
  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hpow : 2 ^ Fintype.card S =
      2 * 2 ^ (Fintype.card S - 1) := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) :=
        congrArg (fun k : ℕ => 2 ^ k) (by omega)
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (Fintype.card S - 1) := by omega
  rw [hsdiff, huniv, hpow] at hcards
  omega

#check _root_.putnam_1964_b2
#print axioms _root_.putnam_1964_b2
