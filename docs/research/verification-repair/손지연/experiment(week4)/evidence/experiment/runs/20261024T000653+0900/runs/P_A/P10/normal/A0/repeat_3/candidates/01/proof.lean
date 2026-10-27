by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩
  let d_next := BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩

  have h_d_i_pos : 0 < d_i := by
    dsimp [d_i, BBF_CodeDistance]
    omega

  have hC : Nonempty C_i := by
    simp only [nonempty_subtype, C_i]
    exact Submodule.nonempty _

  obtain ⟨g, hg, hmin⟩ : ∃ g ∈ C_i, d_fw =
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard := by
    let S := (fun g : C_i =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
    have hS : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have hs := Nat.sInf_mem hS
    unfold d_fw at hs
    rw [Set.mem_image] at hs
    rcases hs with ⟨g, _, rfl⟩
    exact ⟨g, g.property, rfl⟩

  have hdist : (hammingDist f g : ℕ∞) ≤ d_fw * 2 ^ steps := by
    change (Δ₀(f, g) : ℕ∞) ≤ ↑d_fw * ((2 ^ steps : ℕ) : ℕ∞)
    rw [← ENat.coe_mul, ENat.coe_le_coe, hmin]
    set ΔH := Finset.filter (fun x => f x ≠ g x) Finset.univ
    have hΔH : hammingDist f g = ΔH.card := by
      simp [ΔH, hammingDist]
    rw [hΔH]
    set Y := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g
    have hsub : ΔH ⊆ Finset.biUnion Y.toFinset
        (fun y => ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y) ''
          (Finset.univ : Finset (Fin (2 ^ steps)))).toFinset) := by
      intro x hx
      have hfg : f x ≠ g x := by
        simpa [ΔH] using hx
      let y := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x
      have hy : y ∈ Y := by
        simp only [Y, fiberwiseDisagreementSet]
        exact ⟨x, rfl, hfg⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨y, by simpa using hy, ?_⟩
      simp only [coe_univ, Set.image_univ, Set.toFinset_range, mem_image, mem_univ,
        true_and]
      use pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (x := x)
      exact (is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y)).mp rfl
    apply (Finset.card_le_card hsub).trans
    rw [Finset.card_biUnion]
    · simp only [Set.toFinset_card]
      have hcard := card_qMap_total_fiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
      simp only [Set.image_univ, Fintype.card_ofFinset, Subtype.forall] at hcard
      have heach : ∀ y ∈ Y.toFinset,
          Fintype.card ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
            (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y) ''
            ↑(Finset.univ : Finset (Fin (2 ^ steps)))) = 2 ^ steps := by
        intro y _
        have := hcard (a := y) (b := Submodule.coe_mem y)
        simpa only [coe_univ, Set.image_univ, Fintype.card_ofFinset] using this
      rw [Finset.sum_congr rfl heach]
      simp only [sum_const, Set.toFinset_card, smul_eq_mul, ofNat_pos, pow_pos,
        _root_.mul_le_mul_right, ge_iff_le]
      conv_rhs => rw [← _root_.Nat.card_coe_set_eq]
      simp only [card_eq_fintype_card, le_refl]
    · intro y₁ _ y₂ _ hne
      simpa only [Function.onFun, coe_univ] using
        (qMap_total_fiber_disjoint (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by omega) (y₁ := y₁) (y₂ := y₂) (hy_ne := hne))

  have hbridge : d_H ≤ d_fw * 2 ^ steps := by
    apply le_trans (b := hammingDist f g)
    · simp only [distFromCode, SetLike.mem_coe, hammingDist, ne_eq, d_H]
      apply sInf_le
      exact ⟨g, hg, le_rfl⟩
    · exact hdist

  have hfw : 2 * d_fw ≤ d_next - 1 := by
    exact Nat.le_of_lt_succ (WithTop.coe_lt_coe.1 h_fw_dist_lt)

  have hid : (d_next - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_next, BBF_CodeDistance]
    rw [Nat.sub_mul, ← Nat.pow_add, ← Nat.pow_add]
    have h₁ : ℓ + 𝓡 - (i + steps) + steps = ℓ + 𝓡 - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel]
    have h₂ : ℓ - (i + steps) + steps = ℓ - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel]
    rw [h₁, h₂]

  have hfinite : d_H ≠ ⊤ := by
    simp only [ne_eq, d_H]
    rw [Code.distFromCode_eq_top_iff_empty f C_i]
    exact Set.nonempty_iff_ne_empty'.mp hC

  let d_H_nat := ENat.toNat d_H
  have hdH : d_H = d_H_nat := (ENat.coe_toNat hfinite).symm
  have hfinal : 2 * d_H_nat ≤ d_i - 1 := by
    have hn : d_H_nat ≤ d_fw * 2 ^ steps := by
      rw [← ENat.coe_le_coe]
      exact le_of_eq_of_le hdH.symm hbridge
    calc
      2 * d_H_nat ≤ 2 * (d_fw * 2 ^ steps) := by gcongr
      _ = (2 * d_fw) * 2 ^ steps := by rw [mul_assoc]
      _ ≤ (d_next - 1) * 2 ^ steps := by gcongr
      _ = d_i - 1 := hid

  simp only [d_H, d_H_nat] at hdH
  rw [hdH]
  change ((2 : ℕ) : ℕ∞) * ↑Δ₀(f, C_i).toNat <
    ↑(BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩)
  rw [← ENat.coe_mul, ENat.coe_lt_coe]
  exact Nat.lt_of_le_pred h_d_i_pos hfinal