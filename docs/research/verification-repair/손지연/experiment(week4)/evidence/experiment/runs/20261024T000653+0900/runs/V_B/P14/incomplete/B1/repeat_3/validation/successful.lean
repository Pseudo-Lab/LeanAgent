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
  have hup : ∀ {A B : Set S}, A ∈ P → A ⊆ B → B ∈ P := by
    intro A B hA hAB
    by_contra hB
    apply hPS
    refine ⟨B, hB, ?_⟩
    intro U hU
    intro hBU
    apply hPP A hA U hU
    apply Set.Subset.antisymm
    · intro x hx
      have hx' : x ∈ B ∩ U := ⟨hAB hx.1, hx.2⟩
      rw [hBU] at hx'
      exact hx'
    · exact Set.empty_subset _
  have hcomp : ∀ T : Set S, Tᶜ ∈ P ↔ T ∉ P := by
    intro T
    constructor
    · intro hTc hT
      have hne := hPP T hT Tᶜ hTc
      simpa using hne
    · intro hT
      by_contra hTc
      apply hPS
      refine ⟨Tᶜ, hTc, ?_⟩
      intro U hU
      intro hTU
      apply hT
      apply hup hU
      intro x hxU
      by_contra hxT
      have hx : x ∈ Tᶜ ∩ U := ⟨by simp [hxT], hxU⟩
      rw [hTU] at hx
      exact hx
  have himage : P.image (fun T : Set S => Tᶜ) = Pᶜ := by
    ext T
    constructor
    · intro hT
      rcases Finset.mem_image.mp hT with ⟨U, hU, hUT⟩
      subst T
      have hnot : Uᶜ ∉ P := by
        apply (hcomp (Uᶜ)).1
        simpa using hU
      simpa using hnot
    · intro hT
      have hnot : T ∉ P := by
        simpa using hT
      apply Finset.mem_image.mpr
      refine ⟨Tᶜ, (hcomp T).2 hnot, ?_⟩
      simp
  have hcardimage : (P.image (fun T : Set S => Tᶜ)).card = P.card := by
    apply Finset.card_image_iff.mpr
    intro A hA B hB hAB
    have h := congrArg (fun T : Set S => Tᶜ) hAB
    simpa using h
  have hcardcomp : Pᶜ.card = P.card := by
    rw [← himage]
    exact hcardimage
  have hsum : P.card + Pᶜ.card = Fintype.card (Set S) := by
    rw [Finset.card_compl]
    have hle := Finset.card_le_univ P
    omega
  have hdouble : P.card + P.card = 2 ^ Fintype.card S := by
    calc
      P.card + P.card = P.card + Pᶜ.card := by rw [hcardcomp]
      _ = Fintype.card (Set S) := hsum
      _ = 2 ^ Fintype.card S := by simp
  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hpow : 2 ^ Fintype.card S = 2 * 2 ^ (Fintype.card S - 1) := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) :=
        congrArg (fun n : ℕ => 2 ^ n) (by omega)
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (Fintype.card S - 1) := Nat.mul_comm _ _
  rw [hpow] at hdouble
  omega
