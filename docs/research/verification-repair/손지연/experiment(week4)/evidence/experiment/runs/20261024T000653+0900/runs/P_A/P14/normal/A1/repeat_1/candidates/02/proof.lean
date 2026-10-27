by
  classical
  have hdisjoint : ∀ A : Set S, A ∉ P → ∃ U ∈ P, A ∩ U = ∅ := by
    intro A hA
    by_contra h
    apply hPS
    refine ⟨A, hA, ?_⟩
    intro U hU hAU
    exact h ⟨U, hU, hAU⟩

  have hchoice : ∀ A : Set S, A ∈ P ∨ Aᶜ ∈ P := by
    intro A
    by_contra h
    have hA : A ∉ P := fun hA => h (Or.inl hA)
    have hAc : Aᶜ ∉ P := fun hAc => h (Or.inr hAc)
    obtain ⟨U, hU, hAU⟩ := hdisjoint A hA
    obtain ⟨V, hV, hAV⟩ := hdisjoint Aᶜ hAc
    apply (hPP U hU V hV)
    apply Set.eq_empty_of_forall_not_mem
    intro x hx
    have hxA : x ∈ A := by
      by_contra hxA
      have hxAc : x ∈ Aᶜ := by simpa using hxA
      have hx' : x ∈ Aᶜ ∩ V := ⟨hxAc, hx.2⟩
      rw [hAV] at hx'
      simpa using hx'
    have hx' : x ∈ A ∩ U := ⟨hxA, hx.1⟩
    rw [hAU] at hx'
    simpa using hx'

  have hnotboth : ∀ A : Set S, A ∈ P → Aᶜ ∉ P := by
    intro A hA hAc
    exact (hPP A hA Aᶜ hAc) (by simp)

  let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \ P
  have hPQ : ∀ A ∈ P, Aᶜ ∈ Q := by
    intro A hA
    simp only [Q, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact hnotboth A hA
  have hQP : ∀ A ∈ Q, Aᶜ ∈ P := by
    intro A hA
    have hA' : A ∉ P := by
      simpa [Q] using hA
    exact (hchoice A).resolve_left hA'
  have hcard : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
    · exact hPQ
    · exact hQP
    · intro A hA
      simp
    · intro A hA
      simp

  have hd : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro A hA hAQ
    simpa [Q, hA] using hAQ
  have hu : P ∪ Q = (Finset.univ : Finset (Set S)) := by
    ext A
    simp [Q]
  have hsum₀ : P.card + Q.card = (P ∪ Q).card := by
    rw [← Finset.card_union_add_card_inter P Q]
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
    simp
  have hsum : P.card + Q.card = 2 ^ Fintype.card S := by
    calc
      P.card + Q.card = (P ∪ Q).card := hsum₀
      _ = (Finset.univ : Finset (Set S)).card := by rw [hu]
      _ = 2 ^ Fintype.card S := by simp [Fintype.card_fun]

  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hpow : 2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1) * 2 := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) := by
        congr 1
        omega
      _ = 2 ^ (Fintype.card S - 1) * 2 := by
        exact pow_succ 2 _
  omega