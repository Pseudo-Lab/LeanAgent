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
  have hmax (T : Set S) (hT : ∀ U ∈ P, T ∩ U ≠ ∅) : T ∈ P := by
    by_contra hn
    exact hPS ⟨T, hn, hT⟩
  have hcompl (T : Set S) : T ∉ P ↔ Tᶜ ∈ P := by
    constructor
    · intro hT
      have hex : ∃ U ∈ P, T ∩ U = ∅ := by
        by_contra hx
        apply hT
        apply hmax T
        intro U hU hTU
        apply hx
        exact ⟨U, hU, hTU⟩
      rcases hex with ⟨U, hU, hTU⟩
      apply hmax Tᶜ
      intro V hV
      intro hTV
      have huv : U ∩ V ≠ ∅ := hPP U hU V hV
      apply huv
      ext x
      constructor
      · intro hx
        have hxTc : x ∈ Tᶜ := by
          intro hxT
          have hxTU : x ∈ T ∩ U := ⟨hxT, hx.1⟩
          simpa [hTU] using hxTU
        have hxTcV : x ∈ Tᶜ ∩ V := ⟨hxTc, hx.2⟩
        simpa [hTV] using hxTcV
      · intro hx
        exact hx.elim
    · intro hTc hT
      have h := hPP T hT Tᶜ hTc
      exact h (by simp)
  let e : {T : Set S // T ∈ P} ≃ {T : Set S // T ∉ P} :=
    { toFun := fun T =>
        ⟨T.1ᶜ, by
          intro hTc
          have h := hPP T.1 T.2 T.1ᶜ hTc
          exact h (by simp)⟩
      invFun := fun T =>
        ⟨T.1ᶜ, (hcompl T.1).1 T.2⟩
      left_inv := by
        intro T
        apply Subtype.ext
        simp
      right_inv := by
        intro T
        apply Subtype.ext
        simp }
  have hcard : P.card = 2 ^ Fintype.card S - P.card := by
    simpa using Fintype.card_congr e
  have hpowpos : 0 < 2 ^ Fintype.card S := by
    positivity
  have hsum : P.card + P.card = 2 ^ Fintype.card S := by
    omega
  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hn' : Fintype.card S = (Fintype.card S - 1) + 1 := by
    omega
  have hp : 2 ^ Fintype.card S = 2 * 2 ^ (Fintype.card S - 1) := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) :=
        congrArg (fun k : ℕ => 2 ^ k) hn'
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (Fintype.card S - 1) := by omega
  rw [hp] at hsum
  omega

#check _root_.putnam_1964_b2
#print axioms _root_.putnam_1964_b2
