by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩
  let d_next := BBF_CodeDistance ℓ 𝓡 ⟨i.val + steps, by omega⟩
  have h_d_i_pos : 0 < d_i := by
    dsimp [d_i, BBF_CodeDistance]
    have he : ℓ - i.val < ℓ + 𝓡 - i.val := by
      exact Nat.sub_lt_sub_right (a := ℓ) (b := ℓ + 𝓡) (c := i.val) (by omega)
        (by apply Nat.lt_add_of_pos_right; exact pos_of_neZero 𝓡)
    have hp : 2 ^ (ℓ - i.val) < 2 ^ (ℓ + 𝓡 - i.val) :=
      Nat.pow_lt_pow_right (by norm_num) he
    omega
  have hC : Nonempty C_i := by
    simp only [nonempty_subtype, C_i]
    exact Submodule.nonempty
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val, by omega⟩)
  obtain ⟨g, hgC, hmin⟩ : ∃ g ∈ C_i, d_fw =
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard := by
    let S := (fun g : C_i =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
    have hS : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have hs := Nat.sInf_mem hS
    unfold d_fw at hs
    rw [Set.mem_image] at hs
    rcases hs with ⟨g, _, hg⟩
    exact ⟨g.val, g.property, hg.symm⟩
  have hdist : (hammingDist f g : ℕ∞) ≤ d_fw * 2 ^ steps := by
    change (Δ₀(f, g) : ℕ∞) ≤ ↑d_fw * ((2 ^ steps : ℕ) : ℕ∞)
    rw [← ENat.coe_mul, ENat.coe_le_coe, hmin]
    let ΔH := Finset.filter (fun x => f x ≠ g x) Finset.univ
    have hΔH : hammingDist f g = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [hΔH]
    let Y := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g
    simp only at *
    have hsub : ΔH ⊆ Finset.biUnion Y.toFinset
        (fun y => ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)) ''
          (Finset.univ : Finset (Fin (2 ^ steps)))).toFinset) := by
      intro x hx
      simp only [ΔH, Finset.mem_filter] at hx
      let yx := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x
      apply Finset.mem_biUnion.mpr
      use yx
      have hy : yx ∈ Y.toFinset := by
        simp only [fiberwiseDisagreementSet, iteratedQuotientMap, ne_eq, Subtype.exists,
          Set.toFinset_setOf, mem_filter, mem_univ, true_and, Y]
        let X := x.val
        have hX : X ∈ sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) :=
          Submodule.coe_mem x
        use X
        use hX
        have hq : Polynomial.eval X
            (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
              ⟨steps, by simp only; omega⟩) = yx := by
          simp only [iteratedQuotientMap, X, yx]
        have hne : f ⟨X, by omega⟩ ≠ g ⟨X, by omega⟩ := by
          unfold X
          simpa only [Subtype.coe_eta, ne_eq] using hx.2
        simp only [hq, Subtype.coe_eta, hne, not_false_eq_true, and_self]
      simp only [hy, true_and, coe_univ, Set.image_univ, Set.toFinset_range, mem_image,
        mem_univ, true_and]
      use pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (x := x)
      exact (is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := yx)).mp rfl
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_biUnion]
    · simp only [Set.toFinset_card]
      have hc := card_qMap_total_fiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
      simp only [Set.image_univ, Fintype.card_ofFinset, Subtype.forall] at hc
      have h_each : ∀ y ∈ Y.toFinset,
          Fintype.card ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
            (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)) ''
            ↑(Finset.univ : Finset (Fin (2 ^ steps)))) = 2 ^ steps := by
        intro y hy
        have := hc (a := y) (b := Submodule.coe_mem y)
        simpa only [coe_univ, Set.image_univ, Fintype.card_ofFinset] using this
      rw [Finset.sum_congr rfl h_each]
      simp only [sum_const, Set.toFinset_card, smul_eq_mul, ofNat_pos, pow_pos,
        _root_.mul_le_mul_right, ge_iff_le]
      conv_rhs => rw [← _root_.Nat.card_coe_set_eq]
      simp only [card_eq_fintype_card, le_refl]
    · intro y₁ hy₁ y₂ hy₂ hne
      simpa only [Function.onFun, coe_univ] using
        (qMap_total_fiber_disjoint (𝔽q := 𝔽q) (β := β)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by omega) (y₁ := y₁) (y₂ := y₂) hne)
  have hbridge : d_H ≤ d_fw * 2 ^ steps := by
    refine le_trans ?_ hdist
    simp only [distFromCode, SetLike.mem_coe, hammingDist, ne_eq, d_H]
    apply sInf_le
    exact ⟨g, hgC, le_rfl⟩
  have hfw : 2 * d_fw ≤ d_next - 1 :=
    Nat.le_of_lt_succ (WithTop.coe_lt_coe.1 h_fw_dist_lt)
  have hid : (d_next - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_next, BBF_CodeDistance]
    rw [Nat.sub_mul, ← Nat.pow_add, ← Nat.pow_add]
    have h₁ : ℓ + 𝓡 - (i + steps) + steps = ℓ + 𝓡 - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel (n := i) (m := steps)]
    have h₂ : ℓ - (i + steps) + steps = ℓ - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel (n := i) (m := steps)]
    rw [h₁, h₂]
  have hdH : d_H ≠ ⊤ := by
    simp only [ne_eq, d_H]
    rw [Code.distFromCode_eq_top_iff_empty f C_i]
    exact Set.nonempty_iff_ne_empty'.mp hC
  let dH := ENat.toNat d_H
  have hdH_eq : d_H = dH := (ENat.coe_toNat hdH).symm
  have hfinal : 2 * dH ≤ d_i - 1 := by
    have hb : dH ≤ d_fw * 2 ^ steps := by
      rw [← ENat.coe_le_coe]
      exact le_of_eq_of_le hdH_eq.symm hbridge
    calc
      2 * dH ≤ 2 * (d_fw * 2 ^ steps) := by gcongr
      _ = (2 * d_fw) * 2 ^ steps := by rw [mul_assoc]
      _ ≤ (d_next - 1) * 2 ^ steps := by gcongr
      _ = d_i - 1 := hid
  simp only [d_H, dH] at hdH_eq
  rw [hdH_eq]
  change ((2 : ℕ) : ℕ∞) * ↑Δ₀(f, C_i).toNat <
    ↑(BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩)
  rw [← ENat.coe_mul, ENat.coe_lt_coe]
  exact Nat.lt_of_le_pred h_d_i_pos hfinal