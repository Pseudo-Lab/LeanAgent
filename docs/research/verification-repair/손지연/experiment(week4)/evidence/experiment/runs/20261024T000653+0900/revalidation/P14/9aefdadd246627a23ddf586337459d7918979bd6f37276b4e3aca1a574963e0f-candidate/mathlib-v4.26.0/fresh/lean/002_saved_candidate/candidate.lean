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
    apply Set.nonempty_iff_ne_empty.mp
    rcases Set.nonempty_iff_ne_empty.mpr (hPP A hA U hU) with ⟨x, hxA, hxU⟩
    exact ⟨x, hAB hxA, hxU⟩
  have hcomp : ∀ T : Set S, T ∈ P ↔ Tᶜ ∉ P := by
    intro T
    constructor
    · intro hT hTc
      have h := hPP T hT Tᶜ hTc
      simpa using h
    · intro hTc
      by_contra hT
      have hex : ∃ U ∈ P, T ∩ U = ∅ := by
        by_contra hn
        push_neg at hn
        apply hPS
        refine ⟨T, hT, ?_⟩
        intro U hU
        exact Set.nonempty_iff_ne_empty.mp (hn U hU)
      rcases hex with ⟨U, hU, hTU⟩
      apply hTc
      apply hup hU
      intro x hxU
      simp only [Set.mem_compl_iff]
      intro hxT
      have hx : x ∈ T ∩ U := ⟨hxT, hxU⟩
      rw [hTU] at hx
      exact hx
  have hcomp' : ∀ T : Set S, Tᶜ ∈ P ↔ T ∉ P := by
    intro T
    simpa using (hcomp Tᶜ)
  let Q : Finset (Set S) := Finset.univ.filter (fun T : Set S => T ∉ P)
  have hQP : Q.card = P.card := by
    let e : {T // T ∈ Q} ≃ {T // T ∈ P} :=
      { toFun := fun T =>
          ⟨T.1ᶜ, (hcomp' T.1).2 (by
            have hTQ : T.1 ∈ Q := T.2
            change T.1 ∈ Finset.univ.filter (fun U : Set S => U ∉ P) at hTQ
            exact (Finset.mem_filter.mp hTQ).2)⟩
        invFun := fun T =>
          ⟨T.1ᶜ, by
            change T.1ᶜ ∈ Finset.univ.filter (fun U : Set S => U ∉ P)
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (hcomp T.1).1 T.2⟩⟩
        left_inv := by
          intro T
          apply Subtype.ext
          simp
        right_inv := by
          intro T
          apply Subtype.ext
          simp }
    simpa using (Fintype.card_congr e)
  have hdisj : Disjoint P Q := by
    refine Finset.disjoint_left.mpr ?_
    intro T hT hTQ
    have hnT : T ∉ P := by
      change T ∈ Finset.univ.filter (fun U : Set S => U ∉ P) at hTQ
      exact (Finset.mem_filter.mp hTQ).2
    exact hnT hT
  have hunion : P ∪ Q = Finset.univ := by
    ext T
    constructor
    · intro _
      exact Finset.mem_univ T
    · intro _
      by_cases hT : T ∈ P
      · exact Finset.mem_union.mpr (Or.inl hT)
      · apply Finset.mem_union.mpr
        right
        change T ∈ Finset.univ.filter (fun U : Set S => U ∉ P)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ T, hT⟩
  have htotal : P.card + Q.card = Fintype.card (Set S) := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    simp
  have hdouble : P.card + P.card = 2 ^ Fintype.card S := by
    calc
      P.card + P.card = P.card + Q.card := by omega
      _ = Fintype.card (Set S) := htotal
      _ = 2 ^ Fintype.card S := by simp
  have hn : 0 < Fintype.card S := Fintype.card_pos_iff.mpr inferInstance
  have hpow :
      2 ^ Fintype.card S =
        2 ^ (Fintype.card S - 1) + 2 ^ (Fintype.card S - 1) := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) := by
        congr 1
        omega
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
      _ = 2 ^ (Fintype.card S - 1) + 2 ^ (Fintype.card S - 1) := by omega
  omega

#check _root_.putnam_1964_b2
#print axioms _root_.putnam_1964_b2
