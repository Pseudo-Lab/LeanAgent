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
  have h_disjoint (A : Set S) (hA : A ∉ P) :
      ∃ U ∈ P, A ∩ U = ∅ := by
    by_contra h
    exact hPS ⟨A, hA, fun U hU hAU => h ⟨U, hU, hAU⟩⟩

  have h_pair (A : Set S) : A ∈ P ∨ Aᶜ ∈ P := by
    by_contra h
    have hA : A ∉ P := fun hA => h (Or.inl hA)
    have hAc : Aᶜ ∉ P := fun hAc => h (Or.inr hAc)
    obtain ⟨U, hU, hAU⟩ := h_disjoint A hA
    obtain ⟨V, hV, hAcV⟩ := h_disjoint Aᶜ hAc
    have hUV : U ∩ V = ∅ := by
      apply Set.eq_empty_of_forall_not_mem
      intro x hx
      have hxA : x ∈ A := by
        by_contra hxA
        have hxAc : x ∈ Aᶜ := by simpa using hxA
        have hempty : x ∈ (∅ : Set S) := hAcV ▸ ⟨hxAc, hx.2⟩
        simpa using hempty
      have hempty : x ∈ (∅ : Set S) := hAU ▸ ⟨hxA, hx.1⟩
      simpa using hempty
    exact (hPP U hU V hV) hUV

  have h_not_both (A : Set S) (hA : A ∈ P) : Aᶜ ∉ P := by
    intro hAc
    exact (hPP A hA Aᶜ hAc) (by simp)

  let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \ P
  have hcard : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
    · intro A hA
      simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact h_not_both A hA
    · intro A hA
      simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and] at hA
      exact (h_pair A).resolve_left hA
    · intros
      simp
    · intros
      simp

  have hsub : P ⊆ (Finset.univ : Finset (Set S)) := by
    intro A hA
    exact Finset.mem_univ A
  have hle : P.card ≤ (Finset.univ : Finset (Set S)).card :=
    Finset.card_le_card hsub
  have htotal :
      P.card + Q.card = (Finset.univ : Finset (Set S)).card := by
    calc
      P.card + Q.card =
          P.card + ((Finset.univ : Finset (Set S)) \ P).card := by rfl
      _ = P.card + ((Finset.univ : Finset (Set S)).card - P.card) := by
        rw [Finset.card_sdiff hsub]
      _ = (Finset.univ : Finset (Set S)).card := by omega
  have huniv :
      (Finset.univ : Finset (Set S)).card = 2 ^ Fintype.card S := by
    simp [Fintype.card_fun]
  have hdouble : P.card * 2 = 2 ^ Fintype.card S := by
    omega
  have hpos : 0 < Fintype.card S :=
    Fintype.card_pos_iff.mpr inferInstance
  have hpred : Fintype.card S - 1 + 1 = Fintype.card S := by
    omega
  rw [← hpred, pow_succ] at hdouble
  omega
