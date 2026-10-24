by
  classical
  have hmiss (T : Set S) (hT : T ∉ P) :
      ∃ U ∈ P, T ∩ U = ∅ := by
    by_contra h
    apply hPS
    refine ⟨T, hT, ?_⟩
    intro U hU hTU
    exact h ⟨U, hU, hTU⟩

  have hor (A : Set S) : A ∈ P ∨ Aᶜ ∈ P := by
    by_contra h
    push_neg at h
    obtain ⟨U, hU, hAU⟩ := hmiss A h.1
    obtain ⟨V, hV, hAV⟩ := hmiss Aᶜ h.2
    apply hPP U hU V hV
    apply Set.eq_empty_of_forall_not_mem
    intro x hx
    by_cases hxA : x ∈ A
    · have hx' : x ∈ A ∩ U := ⟨hxA, hx.1⟩
      simpa [hAU] using hx'
    · have hxAc : x ∈ Aᶜ := by simpa using hxA
      have hx' : x ∈ Aᶜ ∩ V := ⟨hxAc, hx.2⟩
      simpa [hAV] using hx'

  have hnot (A : Set S) (hA : A ∈ P) : Aᶜ ∉ P := by
    intro hAc
    exact (hPP A hA Aᶜ hAc) (by simp)

  let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \ P

  have hPQ : ∀ {A : Set S}, A ∈ P → Aᶜ ∈ Q := by
    intro A hA
    simp [Q, hnot A hA]

  have hQP : ∀ {A : Set S}, A ∈ Q → Aᶜ ∈ P := by
    intro A hA
    have hn : A ∉ P := by simpa [Q] using hA
    exact (hor A).resolve_left hn

  have hcardPQ : P.card = Q.card := by
    let e : {A : Set S // A ∈ P} ≃ {A : Set S // A ∈ Q} :=
      { toFun := fun A => ⟨A.1ᶜ, hPQ A.2⟩
        invFun := fun A => ⟨A.1ᶜ, hQP A.2⟩
        left_inv := by
          intro A
          apply Subtype.ext
          simp
        right_inv := by
          intro A
          apply Subtype.ext
          simp }
    simpa using Fintype.card_congr e

  have hunion : P ∪ Q = (Finset.univ : Finset (Set S)) := by
    ext A
    simp [Q]

  have hinter : P ∩ Q = ∅ := by
    ext A
    simp [Q]

  have hsum :
      P.card + Q.card = (Finset.univ : Finset (Set S)).card := by
    rw [← Finset.card_union_add_card_inter P Q, hunion, hinter]
    simp

  have htotal : P.card + Q.card = 2 ^ Fintype.card S := by
    calc
      P.card + Q.card = (Finset.univ : Finset (Set S)).card := hsum
      _ = 2 ^ Fintype.card S := by simp [Fintype.card_fun]

  have hdouble : P.card * 2 = 2 ^ Fintype.card S := by
    calc
      P.card * 2 = P.card + P.card := by omega
      _ = P.card + Q.card := by rw [hcardPQ]
      _ = 2 ^ Fintype.card S := htotal

  have hpos : 1 ≤ Fintype.card S := by
    have h : 0 < Fintype.card S := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨Classical.choice (inferInstance : Nonempty S)⟩
    omega

  have hsucc : Fintype.card S - 1 + 1 = Fintype.card S := by
    omega

  have hpow :
      2 ^ (Fintype.card S - 1) * 2 = 2 ^ Fintype.card S := by
    calc
      2 ^ (Fintype.card S - 1) * 2 =
          2 ^ (Fintype.card S - 1) * 2 ^ 1 := by norm_num
      _ = 2 ^ (Fintype.card S - 1 + 1) := by rw [← pow_add]
      _ = 2 ^ Fintype.card S := by rw [hsucc]

  nlinarith [hdouble, hpow]