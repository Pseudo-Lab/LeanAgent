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

  have hchoice : ∀ A : Set S, A ∈ P ∨ Aᶜ ∈ P := by
    intro A
    by_cases hA : A ∈ P
    · exact Or.inl hA
    · right
      by_contra hAc
      obtain ⟨U, hU, hAU⟩ := hmiss A hA
      obtain ⟨V, hV, hCV⟩ := hmiss Aᶜ hAc
      apply (hPP U hU V hV)
      apply Set.eq_empty_of_forall_not_mem
      intro x hx
      have hxU : x ∈ U := hx.1
      have hxV : x ∈ V := hx.2
      have hnA : x ∉ A := by
        intro hxA
        have hx' : x ∈ A ∩ U := ⟨hxA, hxU⟩
        simpa [hAU] using hx'
      have hxAc : x ∈ Aᶜ := by simpa using hnA
      have hx' : x ∈ Aᶜ ∩ V := ⟨hxAc, hxV⟩
      simpa [hCV] using hx'

  have hmem (A : Set S) : Aᶜ ∈ P ↔ A ∉ P := by
    constructor
    · intro hAc hA
      exact (hPP A hA Aᶜ hAc) (by simp)
    · intro hA
      rcases hchoice A with h | h
      · exact False.elim (hA h)
      · exact h

  let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \ P
  have hcard : P.card = Q.card := by
    let e : {A // A ∈ P} ≃ {A // A ∈ Q} :=
      { toFun := fun A => ⟨A.1ᶜ, by
          simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
          intro hAc
          exact (hmem A.1).1 hAc A.2⟩
        invFun := fun A => ⟨A.1ᶜ, by
          have hA : A.1 ∉ P := by
            simpa only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and] using A.2
          exact (hmem A.1).2 hA⟩
        left_inv := by
          intro A
          apply Subtype.ext
          simp
        right_inv := by
          intro A
          apply Subtype.ext
          simp }
    simpa using Fintype.card_congr e

  have hdis : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro A hA hAQ
    have hnA : A ∉ P := by
      simpa only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and] using hAQ
    exact hnA hA

  have hunion : P ∪ Q = (Finset.univ : Finset (Set S)) := by
    ext A
    simp [Q]

  have htotal : P.card + Q.card = 2 ^ Fintype.card S := by
    calc
      P.card + Q.card = (P ∪ Q).card := by
        rw [← Finset.card_union_add_card_inter P Q]
        rw [Finset.disjoint_iff_inter_eq_empty.mp hdis]
        simp
      _ = (Finset.univ : Finset (Set S)).card := by rw [hunion]
      _ = 2 ^ Fintype.card S := by simp [Fintype.card_fun]

  have hdouble : P.card * 2 = 2 ^ Fintype.card S := by
    omega
  have hn : 0 < Fintype.card S := by
    exact Fintype.card_pos_iff.mpr inferInstance
  have hidx : Fintype.card S - 1 + 1 = Fintype.card S := by
    omega
  have hpow : 2 ^ (Fintype.card S - 1) * 2 = 2 ^ Fintype.card S := by
    calc
      2 ^ (Fintype.card S - 1) * 2 =
          2 ^ (Fintype.card S - 1) * 2 ^ 1 := by norm_num
      _ = 2 ^ (Fintype.card S - 1 + 1) := by rw [← pow_add]
      _ = 2 ^ Fintype.card S := by rw [hidx]
  omega
