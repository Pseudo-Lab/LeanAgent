by
  classical
  have h_disjoint (A : Set S) (hA : A ∉ P) :
      ∃ U ∈ P, A ∩ U = ∅ := by
    by_contra h
    apply hPS
    refine ⟨A, hA, ?_⟩
    intro U hU hAU
    exact h ⟨U, hU, hAU⟩
  have h_cover (A : Set S) : A ∈ P ∨ Aᶜ ∈ P := by
    by_contra! h
    rcases h_disjoint A h.1 with ⟨U, hU, hAU⟩
    rcases h_disjoint Aᶜ h.2 with ⟨V, hV, hAV⟩
    apply hPP U hU V hV
    ext x
    constructor
    · rintro ⟨hxU, hxV⟩
      have hxA : x ∈ A := by
        by_contra hxA
        have hx : x ∈ Aᶜ ∩ V := ⟨by simpa, hxV⟩
        rw [hAV] at hx
        exact hx
      have hx : x ∈ A ∩ U := ⟨hxA, hxU⟩
      rw [hAU] at hx
      exact hx
    · simp
  have h_not_both (A : Set S) (hA : A ∈ P) : Aᶜ ∉ P := by
    intro hAc
    simpa using hPP A hA Aᶜ hAc
  let Q : Finset (Set S) := Finset.univ \ P
  have h_toQ : ∀ A ∈ P, Aᶜ ∈ Q := by
    intro A hA
    simp [Q, h_not_both A hA]
  have h_fromQ : ∀ A ∈ Q, Aᶜ ∈ P := by
    intro A hA
    have hAn : A ∉ P := by simpa [Q] using hA
    exact (h_cover A).resolve_left hAn
  have hcard : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ ↦ Aᶜ) (fun A _ ↦ Aᶜ)
    <;> simp_all [Set.ext_iff]
  have hsum : P.card + Q.card = 2 ^ Fintype.card S := by
    rw [← Finset.card_union_add_card_inter P Q]
    simp [Q]
    rw [Finset.union_univ, Finset.card_univ, Fintype.card_set]
  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hp : 2 ^ Fintype.card S =
      2 ^ (Fintype.card S - 1) * 2 := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) :=
        congrArg (fun n : ℕ ↦ 2 ^ n) (by omega)
      _ = _ := pow_succ 2 (Fintype.card S - 1)
  omega