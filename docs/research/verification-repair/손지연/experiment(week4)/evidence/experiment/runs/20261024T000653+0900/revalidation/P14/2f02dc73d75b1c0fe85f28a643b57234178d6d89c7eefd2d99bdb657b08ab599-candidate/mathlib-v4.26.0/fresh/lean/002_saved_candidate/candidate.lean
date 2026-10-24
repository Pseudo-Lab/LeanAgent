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
  have hmax (T : Set S) (hT : T ∉ P) :
      ∃ U ∈ P, T ∩ U = ∅ := by
    by_contra h
    apply hPS
    refine ⟨T, hT, ?_⟩
    intro U hU hTU
    exact h ⟨U, hU, hTU⟩

  have hnotboth (A : Set S) (hA : A ∈ P) : Aᶜ ∉ P := by
    intro hAc
    simpa using hPP A hA Aᶜ hAc

  have hone (A : Set S) : A ∈ P ∨ Aᶜ ∈ P := by
    by_cases hA : A ∈ P
    · exact Or.inl hA
    · right
      by_contra hAc
      obtain ⟨U, hU, hU0⟩ := hmax Aᶜ hAc
      obtain ⟨V, hV, hV0⟩ := hmax A hA
      apply hPP U hU V hV
      apply Set.eq_empty_of_forall_not_mem
      intro x hx
      rcases hx with ⟨hxU, hxV⟩
      have hxA : x ∉ A := by
        intro hxA
        have hxAV : x ∈ A ∩ V := ⟨hxA, hxV⟩
        simpa [hV0] using hxAV
      have hxCU : x ∈ Aᶜ ∩ U := ⟨hxA, hxU⟩
      simpa [hU0] using hxCU

  let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \ P
  have hcard : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
    · intro A hA
      simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hnotboth A hA
    · intro A hA
      simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and] at hA ⊢
      exact (hone A).resolve_left hA
    · intro A hA
      simp
    · intro A hA
      simp

  have hdis : P ∩ Q = ∅ := by
    ext A
    simp [Q]
  have hunion : P ∪ Q = (Finset.univ : Finset (Set S)) := by
    ext A
    simp [Q]
  have hsum : P.card + Q.card = 2 ^ Fintype.card S := by
    calc
      P.card + Q.card = (P ∪ Q).card + (P ∩ Q).card :=
        (Finset.card_union_add_card_inter P Q).symm
      _ = 2 ^ Fintype.card S := by
        rw [hunion, hdis]
        simp [Fintype.card_fun]
  have hdouble : P.card * 2 = 2 ^ Fintype.card S := by
    calc
      P.card * 2 = P.card + P.card := by omega
      _ = P.card + Q.card := congrArg (fun n => P.card + n) hcard
      _ = 2 ^ Fintype.card S := hsum
  have hn : 0 < Fintype.card S :=
    Fintype.card_pos_iff.mpr (inferInstance : Nonempty S)
  rw [show Fintype.card S = (Fintype.card S - 1) + 1 by omega,
    pow_succ] at hdouble
  omega

#check _root_.putnam_1964_b2
#print axioms _root_.putnam_1964_b2
