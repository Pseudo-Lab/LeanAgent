by
  classical
  have hmax (T : Set S) (hT : ∀ U ∈ P, T ∩ U ≠ ∅) : T ∈ P := by
    by_contra hn
    exact hPS ⟨T, hn, hT⟩
  have hcompl (T : Set S) : T ∉ P ↔ Tᶜ ∈ P := by
    constructor
    · intro hT
      have hex : ∃ U ∈ P, T ∩ U = ∅ := by
        by_contra hx
        push_neg at hx
        exact hT (hmax T hx)
      rcases hex with ⟨U, hU, hTU⟩
      apply hmax Tᶜ
      intro V hV
      intro hTV
      have huv : U ∩ V ≠ ∅ := hPP U hU V hV
      apply huv
      ext x
      constructor
      · intro hx
        have hxTc : x ∈ Tᶜ := by
          intro hxT
          have hxTU : x ∈ T ∩ U := ⟨hxT, hx.1⟩
          simpa [hTU] using hxTU
        have hxTcV : x ∈ Tᶜ ∩ V := ⟨hxTc, hx.2⟩
        simpa [hTV] using hxTcV
      · intro hx
        exact hx.elim
    · intro hTc hT
      have h := hPP T hT Tᶜ hTc
      exact h (by simp)
  let e : {T : Set S // T ∈ P} ≃ {T : Set S // T ∈ Pᶜ} :=
    { toFun := fun T =>
        ⟨T.1ᶜ, by
          simp only [Finset.mem_compl]
          exact (hcompl T.1ᶜ).2 (by simpa using T.2)⟩
      invFun := fun T =>
        ⟨T.1ᶜ, by
          have hT : T.1 ∉ P := by simpa using T.2
          exact (hcompl T.1).1 hT⟩
      left_inv := by
        intro T
        apply Subtype.ext
        simp
      right_inv := by
        intro T
        apply Subtype.ext
        simp }
  have hcard : P.card = Pᶜ.card := by
    simpa using Fintype.card_congr e
  have hsum : P.card + P.card = 2 ^ Fintype.card S := by
    calc
      P.card + P.card = P.card + Pᶜ.card :=
        congrArg (fun n : ℕ => P.card + n) hcard
      _ = Fintype.card (Set S) := Finset.card_add_card_compl P
      _ = 2 ^ Fintype.card S := by simp
  have hn : 0 < Fintype.card S := Fintype.card_pos
  have hn' : Fintype.card S = (Fintype.card S - 1) + 1 := by
    omega
  have hp : 2 ^ Fintype.card S = 2 * 2 ^ (Fintype.card S - 1) := by
    calc
      2 ^ Fintype.card S = 2 ^ ((Fintype.card S - 1) + 1) := by rw [hn']
      _ = 2 ^ (Fintype.card S - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (Fintype.card S - 1) := by omega
  rw [hp] at hsum
  omega