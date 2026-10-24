by
  classical
  have hcover (A : Set S) : A ∈ P ∨ Aᶜ ∈ P := by
    by_contra h
    simp only [not_or] at h
    have hA : ∃ U ∈ P, A ∩ U = ∅ := by
      by_contra hn
      push_neg at hn
      exact hPS ⟨A, h.1, hn⟩
    have hAc : ∃ V ∈ P, Aᶜ ∩ V = ∅ := by
      by_contra hn
      push_neg at hn
      exact hPS ⟨Aᶜ, h.2, hn⟩
    obtain ⟨U, hU, hAU⟩ := hA
    obtain ⟨V, hV, hAcV⟩ := hAc
    exact (hPP U hU V hV) (by
      apply Set.eq_empty_of_forall_not_mem
      intro x hx
      have hxnotA : x ∉ A := by
        intro hxA
        have hxAU : x ∈ A ∩ U := ⟨hxA, hx.1⟩
        rw [hAU] at hxAU
        simpa using hxAU
      have hxnotAc : x ∉ Aᶜ := by
        intro hxAc
        have hxAcV : x ∈ Aᶜ ∩ V := ⟨hxAc, hx.2⟩
        rw [hAcV] at hxAcV
        simpa using hxAcV
      exact hxnotA (by simpa using hxnotAc))
  have hnotboth (A : Set S) (hA : A ∈ P) : Aᶜ ∉ P := by
    intro hAc
    exact (hPP A hA Aᶜ hAc) (by simp)
  let Q : Finset (Set S) := Finset.univ \ P
  have hf : ∀ A ∈ P, Aᶜ ∈ Q := by
    intro A hA
    simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact hnotboth A hA
  have hg : ∀ A ∈ Q, Aᶜ ∈ P := by
    intro A hA
    have hn : A ∉ P := by simpa [Q] using hA
    exact (hcover A).resolve_left hn
  have hcard : P.card = Q.card := by
    refine Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ) ?_ ?_ ?_ ?_
    · exact hf
    · exact hg
    · intro A hA
      simp
    · intro A hA
      simp
  have hsum : Q.card + P.card = (Finset.univ : Finset (Set S)).card := by
    simpa [Q] using
      (Finset.card_sdiff_add_card_eq_card
        (show P ⊆ (Finset.univ : Finset (Set S)) by simp))
  have hdouble : P.card + P.card = 2 ^ Fintype.card S := by
    calc
      P.card + P.card = Q.card + P.card := by rw [hcard]
      _ = (Finset.univ : Finset (Set S)).card := hsum
      _ = 2 ^ Fintype.card S := by simp [Fintype.card_fun]
  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hpow :
      2 ^ Fintype.card S =
        2 ^ (Fintype.card S - 1) + 2 ^ (Fintype.card S - 1) := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) :=
        congrArg (fun k : ℕ => 2 ^ k) (by omega)
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
      _ = 2 ^ (Fintype.card S - 1) + 2 ^ (Fintype.card S - 1) := by omega
  omega