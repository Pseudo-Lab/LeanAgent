by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩
  have h_d_i_gt_0 : d_i > 0 := by
    dsimp [d_i, BBF_CodeDistance]
    have he : ℓ - i.val < ℓ + 𝓡 - i.val :=
      Nat.sub_lt_sub_right (by omega) (Nat.lt_add_of_pos_right (pos_of_neZero 𝓡))
    have hp : 2 ^ (ℓ - i.val) < 2 ^ (ℓ + 𝓡 - i.val) :=
      Nat.pow_lt_pow_right (by norm_num) he
    omega
  have h_C_i_nonempty : Nonempty C_i := by
    simp only [nonempty_subtype, C_i]
    exact Submodule.nonempty _
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw =
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').ncard := by
    let S := (fun g : C_i =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
    have hm := Nat.sInf_mem (Set.image_nonempty.mpr Set.univ_nonempty : S.Nonempty)
    rw [Set.mem_image] at hm
    rcases hm with ⟨g, _, hg⟩
    exact ⟨g, g.property, hg.symm⟩
  have h_dist_le : (hammingDist f g' : ℕ∞) ≤ d_fw * 2 ^ steps := by
    change (Δ₀(f, g') : ℕ∞) ≤ ↑d_fw * ((2 ^ steps : ℕ) : ℕ∞)
    rw [← ENat.coe_mul, ENat.coe_le_coe, h_g'_min_card]
    set ΔH := Finset.filter (fun x => f x ≠ g' x) Finset.univ
    have hd : hammingDist f g' = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [hd]
    set Y := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g'
    letI : Fintype Y := Fintype.ofFinite Y
    let A := fun y : Y =>
      ((qMap_total_fiber (ℓ := ℓ) (𝓡 := 𝓡) 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (y := y)) ''
        (Finset.univ : Finset (Fin (2 ^ steps)))).toFinset
    have hs : ΔH ⊆ Finset.biUnion Y.toFinset A := by
      intro x hx
      simp only [ΔH, Finset.mem_filter] at hx
      let y := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x
      have hy : y ∈ Y := ⟨x, rfl, hx.2⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨y, hy⟩, by simp, ?_⟩
      simp only [A, Set.mem_toFinset, Set.mem_image]
      refine ⟨pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (x := x), by simp, ?_⟩
      exact (is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y)).mp rfl
    have hc := card_qMap_total_fiber (ℓ := ℓ) (𝓡 := 𝓡) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
    simp only [Set.image_univ, Fintype.card_ofFinset, Subtype.forall] at hc
    have hc' : ∀ y ∈ Y.toFinset, (A y).card = 2 ^ steps := by
      intro y _
      have h := hc (a := y) (b := Submodule.coe_mem y)
      simpa only [A, coe_univ, Set.image_univ, Fintype.card_ofFinset] using h
    calc
      ΔH.card ≤ (Finset.biUnion Y.toFinset A).card := Finset.card_le_card hs
      _ ≤ ∑ y ∈ Y.toFinset, (A y).card := Finset.card_biUnion_le
      _ = Y.ncard * 2 ^ steps := by
        rw [Finset.sum_congr rfl hc']
        simp only [sum_const, smul_eq_mul, Set.toFinset_card]
  have h_dist_bridge : d_H ≤ (d_fw : ℕ∞) * ((2 ^ steps : ℕ) : ℕ∞) := by
    calc
      d_H ≤ (hammingDist f g' : ℕ∞) := by
        simp only [distFromCode, SetLike.mem_coe, hammingDist, ne_eq, d_H]
        apply sInf_le
        exact ⟨g', h_g'_mem, le_rfl⟩
      _ ≤ (d_fw : ℕ∞) * ((2 ^ steps : ℕ) : ℕ∞) := h_dist_le
  have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 :=
    Nat.le_of_lt_succ (WithTop.coe_lt_coe.1 h_fw_dist_lt)
  have h_identity : (d_i_plus_steps - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_i_plus_steps, BBF_CodeDistance]
    rw [Nat.sub_mul, ← Nat.pow_add, ← Nat.pow_add]
    have h1 : ℓ + 𝓡 - (i + steps) + steps = ℓ + 𝓡 - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel]
    have h2 : ℓ - (i + steps) + steps = ℓ - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel]
    rw [h1, h2]
  have h_dH_ne_top : d_H ≠ ⊤ := by
    simp only [ne_eq, d_H]
    rw [Code.distFromCode_eq_top_iff_empty f C_i]
    exact Set.nonempty_iff_ne_empty'.mp h_C_i_nonempty
  let d_H_nat := ENat.toNat d_H
  have h_dH_eq : d_H = d_H_nat := (ENat.coe_toNat h_dH_ne_top).symm
  have h_final : 2 * d_H_nat ≤ d_i - 1 := by
    have hb : d_H_nat ≤ d_fw * 2 ^ steps := by
      apply ENat.coe_le_coe.mp
      simpa only [ENat.coe_mul] using h_dH_eq.symm.le.trans h_dist_bridge
    calc
      2 * d_H_nat ≤ 2 * (d_fw * 2 ^ steps) := by gcongr
      _ = (2 * d_fw) * 2 ^ steps := by rw [mul_assoc]
      _ ≤ (d_i_plus_steps - 1) * 2 ^ steps := by gcongr
      _ = d_i - 1 := h_identity
  simp only [d_H, d_H_nat] at h_dH_eq
  rw [h_dH_eq]
  change ((2 : ℕ) : ℕ∞) * ↑Δ₀(f, C_i).toNat <
    ↑(BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩)
  rw [← ENat.coe_mul, ENat.coe_lt_coe]
  exact Nat.lt_of_le_pred h_d_i_gt_0 h_final