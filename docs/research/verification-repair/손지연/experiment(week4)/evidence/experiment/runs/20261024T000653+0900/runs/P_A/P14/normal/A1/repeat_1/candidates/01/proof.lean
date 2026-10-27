by
  classical
  have hmax : ∀ A : Set S, A ∉ P → ∃ U ∈ P, A ∩ U = ∅ := by
    intro A hA
    by_contra h
    push_neg at h
    exact hPS ⟨A, hA, h⟩
  have hcover : ∀ A : Set S, A ∈ P ∨ Aᶜ ∈ P := by
    intro A
    by_contra hA
    push_neg at hA
    obtain ⟨U, hU, hAU⟩ := hmax A hA.1
    obtain ⟨V, hV, hAV⟩ := hmax Aᶜ hA.2
    apply (hPP U hU V hV)
    ext x
    simp only [Set.mem_inter_iff, Set.not_mem_empty, iff_false]
    rintro ⟨hxU, hxV⟩
    have hxA : x ∉ A := by
      intro hxA
      have hx : x ∈ A ∩ U := ⟨hxA, hxU⟩
      rw [hAU] at hx
      simpa using hx
    have hx : x ∈ Aᶜ ∩ V := ⟨by simpa, hxV⟩
    rw [hAV] at hx
    simpa using hx
  have hnot : ∀ A : Set S, A ∈ P → Aᶜ ∉ P := by
    intro A hA hAc
    exact (hPP A hA Aᶜ hAc) (Set.inter_compl_self A)
  have hiff : ∀ A : Set S, Aᶜ ∈ P ↔ A ∉ P := by
    intro A
    constructor
    · intro hAc hA
      exact hnot A hA hAc
    · intro hA
      rcases hcover A with hA' | hAc
      · exact (hA hA').elim
      · exact hAc
  let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \ P
  have hcard : P.card = Q.card := by
    apply Finset.card_bij' (fun A _ => Aᶜ) (fun A _ => Aᶜ) <;>
      simp_all [Q, hiff]
  have hUnion : P ∪ Q = (Finset.univ : Finset (Set S)) := by
    ext A
    simp [Q]
  have hInter : P ∩ Q = ∅ := by
    ext A
    simp [Q]
  have huniv : (Finset.univ : Finset (Set S)).card = 2 ^ Fintype.card S := by
    simp [Fintype.card_fun]
  have htotal : P.card + Q.card = 2 ^ Fintype.card S := by
    calc
      P.card + Q.card = (P ∪ Q).card + (P ∩ Q).card :=
        (Finset.card_union_add_card_inter P Q).symm
      _ = 2 ^ Fintype.card S := by rw [hUnion, hInter, huniv]; simp
  have htwo : P.card * 2 = 2 ^ Fintype.card S := by
    omega
  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hn' : Fintype.card S - 1 + 1 = Fintype.card S := by
    omega
  have hpow : 2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1) * 2 := by
    calc
      2 ^ Fintype.card S = 2 ^ (Fintype.card S - 1 + 1) := by rw [hn']
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
  omega