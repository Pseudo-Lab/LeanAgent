theorem putnam_1964_b2
(S : Type*) [Fintype S] [Nonempty S]
(P : Finset (Set S))
(hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅)
(hPS : ¬∃ T : Set S, T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅))
: (P.card = 2 ^ (Fintype.card S - 1)) := by
  classical
  have hP : (P : Set (Set S)).Intersecting := by
    simpa [Set.Intersecting, Set.disjoint_iff_inter_eq_empty] using hPP
  have hcard := hP.is_max_iff_card_eq.mp (by
    intro Q hQ hPQ
    apply Finset.Subset.antisymm hPQ
    intro T hT
    by_contra hT'
    exact hPS ⟨T, hT', fun U hU => by
      simpa [Set.disjoint_iff_inter_eq_empty] using hQ hT (hPQ hU)⟩)
  have hn := Fintype.card_pos (α := S)
  rw [Fintype.card_set, show Fintype.card S = (Fintype.card S - 1) + 1 by omega, pow_succ] at hcard
  omega
