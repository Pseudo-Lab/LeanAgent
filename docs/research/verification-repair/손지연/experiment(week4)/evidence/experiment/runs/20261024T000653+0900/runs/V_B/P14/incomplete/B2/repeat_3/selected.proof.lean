by
  classical
  have hbad : ∀ T : Set S, T ∉ P → ∃ U ∈ P, T ∩ U = ∅ := by
    intro T hT
    by_contra h
    apply hPS
    refine ⟨T, hT, ?_⟩
    intro U hU hTU
    apply h
    exact ⟨U, hU, hTU⟩
  have hchoice : ∀ T : Set S, T ∈ P ∨ Tᶜ ∈ P := by
    intro T
    by_contra h
    push_neg at h
    obtain ⟨hT, hTc⟩ := h
    obtain ⟨U, hU, hTU⟩ := hbad T hT
    obtain ⟨V, hV, hTV⟩ := hbad (Tᶜ) hTc
    have hUV : U ∩ V = ∅ := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hx with ⟨hxU, hxV⟩
        by_cases hxT : x ∈ T
        · rw [← hTU]
          exact ⟨hxT, hxU⟩
        · have hxTc : x ∈ Tᶜ := by
            change x ∉ T
            exact hxT
          rw [← hTV]
          exact ⟨hxTc, hxV⟩
      · exact Set.empty_subset _
    exact (hPP U hU V hV) hUV
  let Q : Finset (Set S) := P.image (fun T : Set S => Tᶜ)
  have hQcard : Q.card = P.card := by
    dsimp [Q]
    apply Finset.card_image_iff.mpr
    intro A hA B hB hAB
    have hc := congrArg (fun T : Set S => Tᶜ) hAB
    simpa using hc
  have hunion : P ∪ Q = Finset.univ := by
    ext T
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases hchoice T with hT | hTc
    · exact Or.inl hT
    · right
      dsimp [Q]
      apply Finset.mem_image.mpr
      exact ⟨Tᶜ, hTc, by simp⟩
  have hdisj : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro T hTP hTQ
    dsimp [Q] at hTQ
    rw [Finset.mem_image] at hTQ
    obtain ⟨U, hUP, hUT⟩ := hTQ
    apply (hPP T hTP U hUP)
    rw [← hUT]
    simp
  have hcunion : (P ∪ Q).card = P.card + Q.card :=
    Finset.card_union_of_disjoint hdisj
  have hcardall : 2 * P.card = 2 ^ Fintype.card S := by
    calc
      2 * P.card = P.card + Q.card := by omega
      _ = (P ∪ Q).card := hcunion.symm
      _ = (Finset.univ : Finset (Set S)).card := by rw [hunion]
      _ = 2 ^ Fintype.card S := by simp
  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hn' : Fintype.card S - 1 + 1 = Fintype.card S := by omega
  have hpow : 2 ^ Fintype.card S =
      2 * 2 ^ (Fintype.card S - 1) := by
    calc
      2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1 + 1) := by rw [hn']
      _ = 2 * 2 ^ (Fintype.card S - 1) := by
        simp [pow_succ, Nat.mul_comm]
  omega