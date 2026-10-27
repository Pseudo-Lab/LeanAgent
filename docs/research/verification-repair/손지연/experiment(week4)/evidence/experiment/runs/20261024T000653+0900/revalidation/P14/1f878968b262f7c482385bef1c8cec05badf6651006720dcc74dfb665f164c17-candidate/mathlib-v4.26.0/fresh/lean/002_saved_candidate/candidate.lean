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
  have hmissing (A : Set S) (hA : A ∉ P) :
      ∃ U ∈ P, A ∩ U = ∅ := by
    by_contra h
    apply hPS
    refine ⟨A, hA, ?_⟩
    intro U hU hAU
    exact h ⟨U, hU, hAU⟩

  have hor (A : Set S) : A ∈ P ∨ Aᶜ ∈ P := by
    by_cases hA : A ∈ P
    · exact Or.inl hA
    by_cases hAc : Aᶜ ∈ P
    · exact Or.inr hAc
    obtain ⟨U, hU, hAU⟩ := hmissing A hA
    obtain ⟨V, hV, hAcV⟩ := hmissing Aᶜ hAc
    have hUV : U ∩ V = ∅ := by
      ext x
      constructor
      · rintro ⟨hxU, hxV⟩
        by_cases hxA : x ∈ A
        · have hx : x ∈ A ∩ U := ⟨hxA, hxU⟩
          rw [hAU] at hx
          exact hx
        · have hxAc : x ∈ Aᶜ := by
            simpa only [Set.mem_compl_iff]
          have hx : x ∈ Aᶜ ∩ V := ⟨hxAc, hxV⟩
          rw [hAcV] at hx
          exact hx
      · simp
    exact (hPP U hU V hV) hUV

  have hnotboth (A : Set S) (hA : A ∈ P) : Aᶜ ∉ P := by
    intro hAc
    exact (hPP A hA Aᶜ hAc) (by simp)

  let C : Finset (Set S) := P.image (fun A : Set S => Aᶜ)
  have hCmem (A : Set S) : A ∈ C ↔ Aᶜ ∈ P := by
    change A ∈ P.image (fun B : Set S => Bᶜ) ↔ Aᶜ ∈ P
    constructor
    · intro h
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp h
      simpa using hB
    · intro h
      exact Finset.mem_image.mpr ⟨Aᶜ, h, by simp⟩

  have hunion : P ∪ C = (Finset.univ : Finset (Set S)) := by
    ext A
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rw [hCmem]
    exact hor A

  have hdisj : Disjoint P C := by
    rw [Finset.disjoint_left]
    intro A hA hAC
    exact hnotboth A hA ((hCmem A).mp hAC)

  have hcardC : C.card = P.card := by
    change (P.image (fun A : Set S => Aᶜ)).card = P.card
    apply Finset.card_image_iff.mpr
    intro A _ B _ h
    have hc := congrArg (fun X : Set S => Xᶜ) h
    simpa using hc

  have hsum : P.card + C.card = (P ∪ C).card := by
    rw [← Finset.card_union_add_card_inter P C]
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
    simp

  have hdouble : P.card + P.card = 2 ^ Fintype.card S := by
    calc
      P.card + P.card = P.card + C.card := by rw [hcardC]
      _ = (P ∪ C).card := hsum
      _ = (Finset.univ : Finset (Set S)).card := by rw [hunion]
      _ = 2 ^ Fintype.card S := by simp [Fintype.card_fun]

  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hn_eq : Fintype.card S = Fintype.card S - 1 + 1 := by
    omega
  have hpow :
      2 ^ Fintype.card S =
        2 ^ (Fintype.card S - 1) + 2 ^ (Fintype.card S - 1) := by
    calc
      2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1 + 1) :=
        congrArg (fun n : ℕ => 2 ^ n) hn_eq
      _ = 2 ^ (Fintype.card S - 1) + 2 ^ (Fintype.card S - 1) := by
        simp [pow_succ, mul_two]
  omega

#check _root_.putnam_1964_b2
#print axioms _root_.putnam_1964_b2
