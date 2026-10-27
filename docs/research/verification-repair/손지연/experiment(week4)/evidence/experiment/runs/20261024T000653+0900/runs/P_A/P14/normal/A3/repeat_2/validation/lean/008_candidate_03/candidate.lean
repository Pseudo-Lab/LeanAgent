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
  have hmiss {A : Set S} (hA : A ∉ P) : ∃ U ∈ P, A ∩ U = ∅ := by
    by_contra h
    push_neg at h
    exact hPS ⟨A, hA, h⟩
  have hexact (A : Set S) : A ∈ P ↔ Aᶜ ∉ P := by
    constructor
    · intro hA hc
      exact hPP A hA Aᶜ hc (by simp)
    · intro hc
      by_contra hA
      obtain ⟨U, hU, hAU⟩ := hmiss hA
      obtain ⟨V, hV, hAV⟩ := hmiss hc
      obtain ⟨x, hxU, hxV⟩ :=
        Set.nonempty_iff_ne_empty.mpr (hPP U hU V hV)
      by_cases hx : x ∈ A
      · have hx' : x ∈ A ∩ U := ⟨hx, hxU⟩
        simp [hAU] at hx'
      · have hx' : x ∈ Aᶜ ∩ V := ⟨hx, hxV⟩
        simp [hAV] at hx'
  have hc : P.card = (Finset.univ \ P).card := by
    apply Finset.card_bij' (fun A _ ↦ Aᶜ) (fun A _ ↦ Aᶜ)
    · intro A hA
      simp
    · intro A hA
      simp
    · intro A hA
      simpa using (hexact A).mp hA
    · intro A hA
      apply (hexact Aᶜ).mpr
      simpa using hA
  rw [Finset.card_sdiff (Finset.subset_univ P)] at hc
  simp at hc
  have hd : P.card * 2 = 2 ^ Fintype.card S := by omega
  have hn : 0 < Fintype.card S := Fintype.card_pos_iff.mpr inferInstance
  have hn' : Fintype.card S = (Fintype.card S - 1) + 1 := by omega
  rw [hn', pow_succ] at hd
  omega

#check _root_.putnam_1964_b2
#print axioms _root_.putnam_1964_b2
