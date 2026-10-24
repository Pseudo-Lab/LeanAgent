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
  have hmax : ∀ A : Set S, A ∉ P → ∃ U ∈ P, A ∩ U = ∅ := by
    intro A hA
    by_contra h
    exact hPS ⟨A, hA, fun U hU hAU => h ⟨U, hU, hAU⟩⟩
  have hcover (A : Set S) : A ∈ P ∨ Aᶜ ∈ P := by
    by_cases hA : A ∈ P
    · exact Or.inl hA
    · right
      by_contra hAc
      obtain ⟨U, hU, hAU⟩ := hmax A hA
      obtain ⟨V, hV, hAcV⟩ := hmax Aᶜ hAc
      obtain ⟨x, hxU, hxV⟩ :=
        Set.nonempty_iff_ne_empty.mpr (hPP U hU V hV)
      have hxA : x ∈ A := by
        by_contra hx
        have hx' : x ∈ Aᶜ ∩ V := ⟨by simpa, hxV⟩
        rw [hAcV] at hx'
        exact hx'
      have hx' : x ∈ A ∩ U := ⟨hxA, hxU⟩
      rw [hAU] at hx'
      exact hx'
  have hnot (A : Set S) (hA : A ∈ P) : Aᶜ ∉ P := fun hAc =>
    (hPP A hA Aᶜ hAc) (by simp)
  let Q : Finset (Set S) := Finset.univ \ P
  have hcard : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
    · intro A hA
      simp
    · intro A hA
      simp
    · intro A hA
      simp [Q, hnot A hA]
    · intro A hA
      exact (hcover A).resolve_left (by simpa [Q] using hA)
  have hQ : Q.card = (Finset.univ : Finset (Set S)).card - P.card := by
    simp [Q, Finset.card_sdiff]
  have hle : P.card ≤ (Finset.univ : Finset (Set S)).card :=
    Finset.card_le_card (Finset.subset_univ P)
  have huniv : (Finset.univ : Finset (Set S)).card = 2 ^ Fintype.card S := by
    simp
  have hp : P.card * 2 = 2 ^ Fintype.card S := by
    omega
  have hn : 0 < Fintype.card S :=
    Fintype.card_pos_iff.mpr inferInstance
  rw [show Fintype.card S = Fintype.card S - 1 + 1 by omega, pow_succ] at hp
  omega
