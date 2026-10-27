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
  have hmax (T : Set S) (hT : T ∉ P) : ∃ U ∈ P, T ∩ U = ∅ := by
    by_contra h
    push_neg at h
    exact hPS ⟨T, hT, h⟩

  have hexact (T : Set S) : T ∈ P ↔ Tᶜ ∉ P := by
    constructor
    · intro hT hTc
      exact (hPP T hT Tᶜ hTc) (by ext x; simp)
    · intro hTc
      by_contra hT
      obtain ⟨U, hU, hTU⟩ := hmax T hT
      obtain ⟨V, hV, hTV⟩ := hmax Tᶜ hTc
      have hUV : U ∩ V = ∅ := by
        apply Set.eq_empty_of_forall_not_mem
        intro x hx
        have hxU : x ∈ U := Set.mem_of_mem_inter_left hx
        have hxV : x ∈ V := Set.mem_of_mem_inter_right hx
        have hxnot : x ∉ T := by
          intro hxT
          have hx' : x ∈ T ∩ U := ⟨hxT, hxU⟩
          rw [hTU] at hx'
          exact hx'
        have hxT : x ∈ T := by
          by_contra hxT
          have hxc : x ∈ Tᶜ := by simpa using hxT
          have hx' : x ∈ Tᶜ ∩ V := ⟨hxc, hxV⟩
          rw [hTV] at hx'
          exact hx'
        exact hxnot hxT
      exact (hPP U hU V hV) hUV

  let Q : Finset (Set S) := Finset.univ \ P
  have htoQ (A : Set S) (hA : A ∈ P) : Aᶜ ∈ Q := by
    simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact (hexact A).mp hA
  have htoP (A : Set S) (hA : A ∈ Q) : Aᶜ ∈ P := by
    have hnA : A ∉ P := by
      simpa only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and] using hA
    apply (hexact Aᶜ).mpr
    simpa using hnA
  have hcardeq : P.card = Q.card := by
    refine Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ) ?_ ?_ ?_ ?_
    · intro A hA
      exact htoQ A hA
    · intro A hA
      exact htoP A hA
    · intro A hA
      simp
    · intro A hA
      simp

  have hdis : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro A hA hAQ
    simp [Q, hA] at hAQ
  have hunion : P ∪ Q = (Finset.univ : Finset (Set S)) := by
    ext A
    simp [Q]
  have htotal : P.card + Q.card = 2 ^ Fintype.card S := by
    calc
      P.card + Q.card = (P ∪ Q).card := by
        rw [← Finset.card_union_add_card_inter]
        rw [Finset.disjoint_iff_inter_eq_empty.mp hdis]
        simp
      _ = (Finset.univ : Finset (Set S)).card := by rw [hunion]
      _ = 2 ^ Fintype.card S := by simp [Fintype.card_fun]
  have hdouble : P.card * 2 = 2 ^ Fintype.card S := by
    omega
  have hpos : 0 < Fintype.card S :=
    Fintype.card_pos_iff.mpr inferInstance
  have hn : Fintype.card S = Fintype.card S - 1 + 1 := by
    omega
  rw [hn, pow_succ] at hdouble
  omega
