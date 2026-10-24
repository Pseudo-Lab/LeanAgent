by
  classical
  have hsep (A : Set S) (hA : A ∉ P) :
      ∃ U ∈ P, A ∩ U = ∅ := by
    by_contra h
    apply hPS
    refine ⟨A, hA, ?_⟩
    intro U hU hAU
    exact h ⟨U, hU, hAU⟩

  have hone (A : Set S) : A ∈ P ∨ Aᶜ ∈ P := by
    by_cases hA : A ∈ P
    · exact Or.inl hA
    · right
      by_contra hAc
      obtain ⟨U, hU, hU'⟩ := hsep A hA
      obtain ⟨V, hV, hV'⟩ := hsep Aᶜ hAc
      apply hPP U hU V hV
      apply Set.eq_empty_of_forall_not_mem
      intro x hx
      have hxA : x ∉ A := by
        intro hxA
        have hx' : x ∈ A ∩ U := ⟨hxA, hx.1⟩
        rw [hU'] at hx'
        exact hx'
      have hx' : x ∈ Aᶜ ∩ V := ⟨by simpa, hx.2⟩
      rw [hV'] at hx'
      exact hx'

  have hnot (A : Set S) (hA : A ∈ P) : Aᶜ ∉ P := by
    intro hAc
    exact (hPP A hA Aᶜ hAc) (by simp)

  let Q : Finset (Set S) := Finset.univ \ P
  have hcardPQ : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
    · intro A hA
      simpa [Q] using hnot A hA
    · intro A hA
      have hn : A ∉ P := by simpa [Q] using hA
      exact (hone A).resolve_left hn
    · intro A hA
      simp
    · intro A hA
      simp

  have hcap : P ∩ Q = ∅ := by
    ext A
    simp [Q]
  have hcup : P ∪ Q = (Finset.univ : Finset (Set S)) := by
    ext A
    simp [Q]
  have hsum : P.card + Q.card = (P ∪ Q).card := by
    rw [← Finset.card_union_add_card_inter P Q, hcap]
    simp
  have htotal : P.card + Q.card = 2 ^ Fintype.card S := by
    calc
      P.card + Q.card = (P ∪ Q).card := hsum
      _ = (Finset.univ : Finset (Set S)).card := congrArg Finset.card hcup
      _ = 2 ^ Fintype.card S := by simp [Fintype.card_fun]

  have hn : 0 < Fintype.card S :=
    Fintype.card_pos_iff.mpr (inferInstance : Nonempty S)
  have hp :
      2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1) * 2 := by
    rw [show Fintype.card S = Fintype.card S - 1 + 1 by omega, pow_succ]
  omega