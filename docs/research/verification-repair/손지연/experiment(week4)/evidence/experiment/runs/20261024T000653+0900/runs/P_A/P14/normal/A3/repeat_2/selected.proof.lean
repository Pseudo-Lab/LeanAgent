by
  classical
  have hmiss {A : Set S} (hA : A ∉ P) : ∃ U ∈ P, A ∩ U = ∅ := by
    by_contra h
    apply hPS
    refine ⟨A, hA, ?_⟩
    intro U hU hAU
    exact h ⟨U, hU, hAU⟩
  have hexact (A : Set S) : A ∈ P ↔ Aᶜ ∉ P := by
    constructor
    · intro hA hc
      simpa using hPP A hA Aᶜ hc
    · intro hc
      by_contra hA
      obtain ⟨U, hU, hAU⟩ := hmiss hA
      obtain ⟨V, hV, hAV⟩ := hmiss hc
      obtain ⟨x, hxU, hxV⟩ :=
        Set.nonempty_iff_ne_empty.mpr (hPP U hU V hV)
      have hxnotA : x ∉ A := by
        intro hxA
        have hx : x ∈ A ∩ U := ⟨hxA, hxU⟩
        simpa [hAU] using hx
      have hxA : x ∈ A := by
        by_contra hxA
        have hx : x ∈ Aᶜ ∩ V := ⟨by simpa, hxV⟩
        simpa [hAV] using hx
      exact hxnotA hxA
  let Q : Finset (Set S) := Finset.univ \ P
  have hf : ∀ A ∈ P, Aᶜ ∈ Q := by
    intro A hA
    simpa [Q] using (hexact A).mp hA
  have hg : ∀ A ∈ Q, Aᶜ ∈ P := by
    intro A hA
    have hn : A ∉ P := by simpa [Q] using hA
    apply (hexact Aᶜ).mpr
    simpa using hn
  have hcard : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ ↦ Aᶜ) (fun A _ ↦ Aᶜ)
    · intro A hA
      simp
    · intro A hA
      simp
    · exact hf
    · exact hg
  have hu : P ∪ Q = (Finset.univ : Finset (Set S)) := by
    ext A
    simp [Q]
  have hi : P ∩ Q = ∅ := by
    ext A
    simp [Q]
  have htotal₀ : P.card + Q.card = (Finset.univ : Finset (Set S)).card := by
    calc
      P.card + Q.card = (P ∪ Q).card + (P ∩ Q).card :=
        (Finset.card_union_add_card_inter P Q).symm
      _ = (Finset.univ : Finset (Set S)).card := by rw [hu, hi]; simp
  have htotal : P.card + Q.card = 2 ^ Fintype.card S := by
    calc
      P.card + Q.card = (Finset.univ : Finset (Set S)).card := htotal₀
      _ = 2 ^ Fintype.card S := by simp
  have hdouble : P.card * 2 = 2 ^ Fintype.card S := by omega
  have hn : 0 < Fintype.card S := Fintype.card_pos_iff.mpr inferInstance
  have hn' : Fintype.card S = (Fintype.card S - 1) + 1 := by omega
  rw [hn', pow_succ] at hdouble
  omega