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
    by_contra h
    push_neg at h
    exact hPS ⟨A, hA, h⟩
  have h_choice : ∀ A : Set S, A ∈ P ∨ Aᶜ ∈ P := by
    intro A
    by_contra h
    have hA : A ∉ P := fun ha => h (Or.inl ha)
    have hAc : Aᶜ ∉ P := fun ha => h (Or.inr ha)
    obtain ⟨U, hU, hAU⟩ := hmiss A hA
    obtain ⟨V, hV, hAcV⟩ := hmiss Aᶜ hAc
    have huv : U ∩ V = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro x hx
      have hxU : x ∈ U := Set.mem_of_mem_inter_left hx
      have hxV : x ∈ V := Set.mem_of_mem_inter_right hx
      have hnA : x ∉ A := by
        intro hxA
        have hx' : x ∈ A ∩ U := ⟨hxA, hxU⟩
        simpa [hAU] using hx'
      have hxA : x ∈ A := by
        by_contra hxA
        have hx' : x ∈ Aᶜ ∩ V := ⟨by simpa, hxV⟩
        simpa [hAcV] using hx'
      exact hnA hxA
    exact (hPP U hU V hV) huv
  have h_not_both : ∀ A : Set S, A ∈ P → Aᶜ ∉ P := by
    intro A hA hAc
    simpa using hPP A hA Aᶜ hAc
  let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \ P
  have hcard : P.card = Q.card := by
    have hf : ∀ A ∈ P, Aᶜ ∈ Q := by
      intro A hA
      simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact h_not_both A hA
    have hg : ∀ A ∈ Q, Aᶜ ∈ P := by
      intro A hA
      have hnA : A ∉ P := by
        simpa only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and] using hA
      exact (h_choice A).resolve_left hnA
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
    <;> simp_all [Set.ext_iff]
  have hdis : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro A hA hAQ
    have hnA : A ∉ P := by simpa [Q] using hAQ
    exact hnA hA
  have hUnion : P ∪ Q = (Finset.univ : Finset (Set S)) := by
    ext A
    simp [Q]
  have hsum : P.card + Q.card = 2 ^ Fintype.card S := by
    calc
      P.card + Q.card = (P ∪ Q).card := by
        rw [← Finset.card_union_add_card_inter P Q]
        rw [Finset.disjoint_iff_inter_eq_empty.mp hdis]
        simp
      _ = (Finset.univ : Finset (Set S)).card := by rw [hUnion]
      _ = 2 ^ Fintype.card S := by simp
  have hdouble : P.card * 2 = 2 ^ Fintype.card S := by
    omega
  have hn : 0 < Fintype.card S := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Classical.choice (inferInstance : Nonempty S)⟩
  have hn' : Fintype.card S - 1 + 1 = Fintype.card S := by
    omega
  have hpow : 2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1) * 2 := by
    calc
      2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1 + 1) := by rw [hn']
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
  omega
