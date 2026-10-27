by
  classical
  have hmiss (A : Set S) (hA : A ∉ P) :
      ∃ U ∈ P, A ∩ U = ∅ := by
    by_contra h
    apply hPS
    refine ⟨A, hA, ?_⟩
    intro U hU hAU
    exact h ⟨U, hU, hAU⟩

  have hpair (A : Set S) : A ∈ P ∨ Aᶜ ∈ P := by
    by_contra h
    have hA : A ∉ P := fun hA => h (Or.inl hA)
    have hAc : Aᶜ ∉ P := fun hAc => h (Or.inr hAc)
    obtain ⟨U, hU, hAU⟩ := hmiss A hA
    obtain ⟨V, hV, hAcV⟩ := hmiss Aᶜ hAc
    have hUV : U ∩ V = ∅ := by
      apply Set.eq_empty_of_forall_not_mem
      intro x hx
      rcases hx with ⟨hxU, hxV⟩
      by_cases hxA : x ∈ A
      · have hx : x ∈ A ∩ U := ⟨hxA, hxU⟩
        rw [hAU] at hx
        simpa using hx
      · have hxAc : x ∈ Aᶜ := by simpa using hxA
        have hx : x ∈ Aᶜ ∩ V := ⟨hxAc, hxV⟩
        rw [hAcV] at hx
        simpa using hx
    exact (hPP U hU V hV) hUV

  have hnot (A : Set S) (hA : A ∈ P) : Aᶜ ∉ P := by
    intro hAc
    exact (hPP A hA Aᶜ hAc) (by simp)

  let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \ P
  have hcardPQ : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
    · intro A hA
      simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hnot A hA
    · intro A hA
      simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and] at hA
      exact (hpair A).resolve_left hA
    · intro A hA
      simp
    · intro A hA
      simp

  have hsum :
      P.card + Q.card = (Finset.univ : Finset (Set S)).card := by
    change P.card + ((Finset.univ : Finset (Set S)) \ P).card =
      (Finset.univ : Finset (Set S)).card
    rw [add_comm]
    apply Finset.card_sdiff_add_card_eq_card
    exact Finset.subset_univ P

  have huniv :
      (Finset.univ : Finset (Set S)).card = 2 ^ Fintype.card S := by
    simp [Fintype.card_fun]
  have hdouble : P.card * 2 = 2 ^ Fintype.card S := by
    omega
  have hn : 0 < Fintype.card S := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Classical.choice (inferInstance : Nonempty S)⟩
  have hpow :
      2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1) * 2 := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) :=
        congrArg (fun k : ℕ => 2 ^ k) (by omega)
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
  rw [hpow] at hdouble
  omega