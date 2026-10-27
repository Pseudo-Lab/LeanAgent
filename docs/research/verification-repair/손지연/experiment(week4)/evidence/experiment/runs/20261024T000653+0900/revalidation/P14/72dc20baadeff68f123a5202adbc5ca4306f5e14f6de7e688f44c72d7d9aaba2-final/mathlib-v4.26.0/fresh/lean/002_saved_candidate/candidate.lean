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
  have hbad (T : Set S) (hT : T ∉ P) :
      ∃ U ∈ P, T ∩ U = ∅ := by
    by_contra h
    apply hPS
    refine ⟨T, hT, ?_⟩
    intro U hU hTU
    apply h
    exact ⟨U, hU, hTU⟩
  have hxor (T : Set S) : T ∈ P ↔ Tᶜ ∉ P := by
    constructor
    · intro hT hTc
      exact (hPP T hT Tᶜ hTc) (by simp)
    · intro hTc
      by_contra hT
      obtain ⟨U, hU, hTU⟩ := hbad T hT
      obtain ⟨V, hV, hTcV⟩ := hbad Tᶜ hTc
      have hUV : U ∩ V = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hxU, hxV⟩
        have hxnotT : x ∉ T := by
          intro hxT
          have hx : x ∈ T ∩ U := ⟨hxT, hxU⟩
          simpa [hTU] using hx
        have hxT : x ∈ T := by
          by_contra hn
          have hxTc : x ∈ Tᶜ := hn
          have hx : x ∈ Tᶜ ∩ V := ⟨hxTc, hxV⟩
          simpa [hTcV] using hx
        exact hxnotT hxT
      exact (hPP U hU V hV) hUV
  let c : Set S → Set S := fun T => Tᶜ
  have hc : Function.Injective c := by
    intro A B h
    have h' := congrArg (fun T : Set S => Tᶜ) h
    simpa [c] using h'
  have hcomp : Pᶜ = P.image c := by
    ext T
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro hT
      have hTc : Tᶜ ∈ P := by
        apply (hxor Tᶜ).2
        simpa using hT
      exact ⟨Tᶜ, hTc, by simp [c]⟩
    · rintro ⟨U, hU, rfl⟩
      simpa [c] using (hxor U).1 hU
  have hcard : (Pᶜ).card = P.card := by
    rw [hcomp]
    exact Finset.card_image_of_injective P hc
  have hdouble : P.card + P.card = Fintype.card (Set S) := by
    calc
      P.card + P.card = (Pᶜ).card + P.card := by rw [hcard]
      _ = Fintype.card (Set S) := Finset.card_compl_add_card P
  have hdouble' : P.card + P.card = 2 ^ Fintype.card S := by
    simpa using hdouble
  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hnrep : Fintype.card S = (Fintype.card S - 1) + 1 := by
    omega
  have hpow :
      2 ^ Fintype.card S =
        2 ^ (Fintype.card S - 1) + 2 ^ (Fintype.card S - 1) := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) :=
        congrArg (fun n : Nat => 2 ^ n) hnrep
      _ = 2 ^ (Fintype.card S - 1) + 2 ^ (Fintype.card S - 1) := by
        simp [pow_succ, mul_two]
  have hh :
      P.card + P.card =
        2 ^ (Fintype.card S - 1) + 2 ^ (Fintype.card S - 1) :=
    hdouble'.trans hpow
  omega

#check _root_.putnam_1964_b2
#print axioms _root_.putnam_1964_b2
