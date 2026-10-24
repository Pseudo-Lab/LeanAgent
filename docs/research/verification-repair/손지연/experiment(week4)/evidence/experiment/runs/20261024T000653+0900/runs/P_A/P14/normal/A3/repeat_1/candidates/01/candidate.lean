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
  have hmiss : ∀ A : Set S, A ∉ P → ∃ U ∈ P, A ∩ U = ∅ := by
    intro A hA
    by_contra! h
    exact hPS ⟨A, hA, h⟩
  have hcover : ∀ A : Set S, A ∈ P ∨ Aᶜ ∈ P := by
    intro A
    by_contra! h
    obtain ⟨U, hU, hAU⟩ := hmiss A h.1
    obtain ⟨V, hV, hAV⟩ := hmiss Aᶜ h.2
    apply hPP U hU V hV
    rw [Set.eq_empty_iff_forall_not_mem] at hAU hAV ⊢
    intro x hx
    by_cases hxA : x ∈ A
    · exact hAU x ⟨hxA, hx.1⟩
    · exact hAV x ⟨by simpa, hx.2⟩
  have hone : ∀ A : Set S, A ∈ P ↔ Aᶜ ∉ P := by
    intro A
    constructor
    · intro hA hAc
      exact hPP A hA Aᶜ hAc (by simp)
    · intro hAc
      rcases hcover A with hA | hA
      · exact hA
      · exact (hAc hA).elim
  let Q : Finset (Set S) := Finset.univ \ P
  have hf : ∀ A ∈ P, Aᶜ ∈ Q := by
    intro A hA
    simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact (hone A).1 hA
  have hg : ∀ A ∈ Q, Aᶜ ∈ P := by
    intro A hA
    have hn : A ∉ P := by
      simpa only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and] using hA
    apply (hone Aᶜ).2
    simpa using hn
  have hc : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
    · exact hf
    · exact hg
    · intro A hA
      simp
    · intro A hA
      simp
  have hu : P ∪ Q = (Finset.univ : Finset (Set S)) := by
    ext A
    simp [Q]
  have hi : P ∩ Q = ∅ := by
    ext A
    simp [Q]
  have ht : P.card + Q.card = 2 ^ Fintype.card S := by
    calc
      P.card + Q.card = (P ∪ Q).card + (P ∩ Q).card :=
        (Finset.card_union_add_card_inter P Q).symm
      _ = 2 ^ Fintype.card S := by rw [hu, hi]; simp
  have hd : P.card * 2 = 2 ^ Fintype.card S := by omega
  have hs : Fintype.card S - 1 + 1 = Fintype.card S := by
    have : 0 < Fintype.card S := Fintype.card_pos
    omega
  have he : 2 ^ (Fintype.card S - 1) * 2 = 2 ^ Fintype.card S := by
    calc
      2 ^ (Fintype.card S - 1) * 2 = 2 ^ (Fintype.card S - 1 + 1) := by rw [pow_succ]
      _ = 2 ^ Fintype.card S := by rw [hs]
  omega
