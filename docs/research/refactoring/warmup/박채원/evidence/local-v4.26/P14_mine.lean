import Mathlib
import Aesop

set_option maxHeartbeats 100000000
set_option Elab.async false

open Set Function Filter Topology

#count_heartbeats in
theorem putnam_1964_b2
(S : Type*) [Fintype S] [Nonempty S]
(P : Finset (Set S))
(hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅)
(hPS : ¬∃ T : Set S, T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅))
: (P.card = 2 ^ (Fintype.card S - 1)) := by
  classical
  -- [핵심] 모든 T 에 대해 "T ∈ P ↔ Tᶜ ∉ P" : 짝 (T, Tᶜ) 마다 정확히 하나
  have key : ∀ T : Set S, T ∈ P ↔ Tᶜ ∉ P := by
    intro T
    constructor
    -- [해설 2] 짝마다 최대 하나: T ∩ Tᶜ = ∅ 이라 둘 다 있으면 교차 조건(hPP)에 모순
    · intro hT hTc
      exact hPP T hT Tᶜ hTc (Set.inter_compl_self T)
    -- [해설 3] 짝마다 최소 하나: T, Tᶜ 가 둘 다 없다고 가정 (귀류법)
    · intro hTc
      by_contra hT
      -- 극대 조건(hPS): T 를 넣을 수 없으니 T 와 겹치지 않는 U ∈ P 가 있음 (U = 해설의 Y)
      obtain ⟨U, hU, hTU⟩ : ∃ U ∈ P, T ∩ U = ∅ := by
        by_contra h
        exact hPS ⟨T, hT, fun U hU hTU => h ⟨U, hU, hTU⟩⟩
      -- Tᶜ 도 넣을 수 없으니 Tᶜ 와 겹치지 않는 V ∈ P 가 있음 (V = 해설의 Z)
      obtain ⟨V, hV, hTV⟩ : ∃ V ∈ P, Tᶜ ∩ V = ∅ := by
        by_contra h
        exact hPS ⟨Tᶜ, hTc, fun V hV hTV => h ⟨V, hV, hTV⟩⟩
      -- U ∩ V = ∅ 을 보이면 교차 조건(hPP)에 모순
      apply hPP U hU V hV
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxU hxV
      by_cases hx : x ∈ T
      · -- x ∈ T 이면 x ∈ T ∩ U = ∅ : 모순 (U ⊆ Tᶜ)
        have : x ∈ T ∩ U := ⟨hx, hxU⟩
        rw [hTU] at this
        exact this
      · -- x ∉ T 이면 x ∈ Tᶜ ∩ V = ∅ : 모순 (V ⊆ T)
        have : x ∈ Tᶜ ∩ V := ⟨hx, hxV⟩
        rw [hTV] at this
        exact this
  -- [해설 4] 개수 세기: P 와 {Tᶜ | T ∈ P} 는 겹치지 않고, 합치면 전체 부분집합
  have hdisj : Disjoint P (P.image compl) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT'
    exact (key U).mp hU hT
  have hunion : P ∪ P.image compl = Finset.univ := by
    ext T
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
    by_cases hT : T ∈ P
    · exact Or.inl hT
    · refine Or.inr ⟨Tᶜ, ?_, compl_compl T⟩
      by_contra h
      exact hT ((key T).mpr h)
  -- |P| + |P| = 2ⁿ (여집합을 취해도 개수는 같음)
  have hcard : P.card + P.card = 2 ^ Fintype.card S := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_image_of_injective _ compl_injective, Finset.card_univ,
      Fintype.card_set] at h
    omega
  -- n ≥ 1 (Nonempty) 이므로 n = m + 1 로 쓰고 2·|P| = 2^(m+1) → |P| = 2^m
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card S = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  rw [hn, pow_succ] at hcard
  rw [hn, Nat.add_sub_cancel]
  omega

#print axioms putnam_1964_b2
