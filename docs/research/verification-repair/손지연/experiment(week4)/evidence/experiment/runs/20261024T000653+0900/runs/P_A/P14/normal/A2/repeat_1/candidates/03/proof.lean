by
  classical
  have hmax (A : Set S) (hA : ∀ U ∈ P, A ∩ U ≠ ∅) : A ∈ P := by
    by_contra hnA
    exact hPS ⟨A, hnA, hA⟩
  have hmem (A : Set S) : A ∈ P ↔ Aᶜ ∉ P := by
    constructor
    · intro hA hAc
      exact hPP A hA Aᶜ hAc (by simp)
    · intro hAc
      apply hmax
      intro U hU hAU
      apply hAc
      apply hmax
      intro V hV hAcV
      apply hPP U hU V hV
      apply Set.eq_empty_of_forall_notMem
      rintro x ⟨hxU, hxV⟩
      have hxA : x ∉ A := by
        intro hxA
        have hx : x ∈ A ∩ U := ⟨hxA, hxU⟩
        simpa [hAU] using hx
      have hx : x ∈ Aᶜ ∩ V := ⟨hxA, hxV⟩
      simpa [hAcV] using hx
  let Q : Finset (Set S) := Finset.univ \ P
  have hc : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ)
    · intro A hA
      simp
    · intro A hA
      simp
    · intro A hA
      simpa [Q] using (hmem A).mp hA
    · intro A hA
      apply (hmem Aᶜ).mpr
      simpa [Q] using hA
  have hsum : P.card + Q.card = (Finset.univ : Finset (Set S)).card := by
    rw [← Finset.card_union_add_card_inter P Q]
    have hi : P ∩ Q = ∅ := by
      ext A
      simp [Q]
    have hu : P ∪ Q = (Finset.univ : Finset (Set S)) := by
      ext A
      simp [Q]
    rw [hi, hu]
    simp
  have hdouble : P.card * 2 = 2 ^ Fintype.card S := by
    calc
      P.card * 2 = P.card + P.card := by omega
      _ = P.card + Q.card := by rw [hc]
      _ = (Finset.univ : Finset (Set S)).card := hsum
      _ = 2 ^ Fintype.card S := by simp
  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hpow : 2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1) * 2 := by
    calc
      2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1 + 1) :=
        congrArg (fun k : ℕ => 2 ^ k) (by omega)
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
  have hcanc : P.card * 2 = 2 ^ (Fintype.card S - 1) * 2 := hdouble.trans hpow
  omega