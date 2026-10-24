by
  classical
  have hcover : ∀ A : Set S, A ∈ P ∨ Aᶜ ∈ P := by
    intro A
    by_contra h
    push_neg at h
    have hA : ¬∀ U ∈ P, A ∩ U ≠ ∅ := by
      intro h'
      exact hPS ⟨A, h.1, h'⟩
    have hAc : ¬∀ U ∈ P, Aᶜ ∩ U ≠ ∅ := by
      intro h'
      exact hPS ⟨Aᶜ, h.2, h'⟩
    push_neg at hA hAc
    obtain ⟨U, hU, hAU⟩ := hA
    obtain ⟨V, hV, hAcV⟩ := hAc
    apply (hPP U hU V hV)
    apply Set.eq_empty_of_forall_not_mem
    intro x hx
    rcases hx with ⟨hxU, hxV⟩
    by_cases hxA : x ∈ A
    · have hx' : x ∈ A ∩ U := ⟨hxA, hxU⟩
      rw [hAU] at hx'
      simpa using hx'
    · have hx' : x ∈ Aᶜ ∩ V := ⟨by simpa, hxV⟩
      rw [hAcV] at hx'
      simpa using hx'
  have hnot : ∀ A : Set S, A ∈ P → Aᶜ ∉ P := by
    intro A hA hAc
    apply hPP A hA Aᶜ hAc
    simp
  let Q : Finset (Set S) := Finset.univ \ P
  have hcard : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
    · intro A hA
      simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hnot A hA
    · intro A hA
      simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and] at hA
      rcases hcover A with hA' | hAc
      · exact (hA hA').elim
      · exact hAc
    · simp
    · simp
  have htotal : Q.card + P.card = (Finset.univ : Finset (Set S)).card := by
    simpa [Q] using Finset.card_sdiff_add_card (Finset.subset_univ P)
  have huniv : (Finset.univ : Finset (Set S)).card = 2 ^ Fintype.card S := by
    simp [Fintype.card_fun]
  have hn : 0 < Fintype.card S := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Classical.choice (inferInstance : Nonempty S)⟩
  have hpow : 2 ^ Fintype.card S = 2 * 2 ^ (Fintype.card S - 1) := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) := by
        rw [show Fintype.card S = Fintype.card S - 1 + 1 by omega]
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (Fintype.card S - 1) := by ac_rfl
  omega