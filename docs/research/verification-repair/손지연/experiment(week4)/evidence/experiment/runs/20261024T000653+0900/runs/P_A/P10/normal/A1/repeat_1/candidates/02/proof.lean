by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i.val + steps, by omega⟩

  have h_d_i_gt_0 : 0 < d_i := by
    dsimp [d_i, BBF_CodeDistance]
    have h_exp_lt : ℓ - i.val < ℓ + 𝓡 - i.val := by
      exact Nat.sub_lt_sub_right (by omega)
        (Nat.lt_add_of_pos_right (pos_of_neZero 𝓡))
    have h_pow_lt : 2 ^ (ℓ - i.val) < 2 ^ (ℓ + 𝓡 - i.val) :=
      Nat.pow_lt_pow_right (by norm_num) h_exp_lt
    omega

  have h_C_i_nonempty : Nonempty C_i := by
    simp only [nonempty_subtype, C_i]
    exact Submodule.nonempty _

  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ :
      ∃ g' ∈ C_i, d_fw =
        (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').ncard := by
    let S := (fun g : C_i =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
    have hS : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have hsInf := Nat.sInf_mem hS
    unfold d_fw at hsInf
    rw [Set.mem_image] at hsInf
    rcases hsInf with ⟨g, _, hg⟩
    exact ⟨g, g.property, hg.symm⟩

  have h_dist_le : (hammingDist f g' : ℕ∞) ≤ d_fw * 2 ^ steps := by
    change (Δ₀(f, g') : ℕ∞) ≤ ↑d_fw * ((2 ^ steps : ℕ) : ℕ∞)
    rw [← ENat.coe_mul, ENat.coe_le_coe, h_g'_min_card]
    set ΔH := Finset.filter (fun x => f x ≠ g' x) Finset.univ
    set Y := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g'
    let q := fun x => iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps
      h_i_add_steps x
    let idx := fun x => pointToIterateQuotientIndex
      (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := h_i_add_steps) (x := x)
    let enc := fun x => (q x, idx x)
    haveI : Fintype Y := Fintype.ofFinite Y
    have h_dist_eq : hammingDist f g' = ΔH.card := by
      simp only [hammingDist, ΔH]
    rw [h_dist_eq]
    calc
      ΔH.card ≤
          (Y.toFinset ×ˢ (Finset.univ : Finset (Fin (2 ^ steps)))).card := by
        apply Finset.card_le_card_of_injOn (f := enc)
        · intro x hx
          have hy : q x ∈ Y.toFinset := by
            rw [Set.mem_toFinset]
            change ∃ z, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps
              h_i_add_steps z = q x ∧ f z ≠ g' z
            exact ⟨x, rfl, (Finset.mem_filter.mp hx).2⟩
          simpa only [enc, Finset.mem_product, Finset.mem_univ, and_true] using hy
        · intro x₁ _ x₂ _ he
          have hq : q x₁ = q x₂ := congrArg Prod.fst he
          have hk : idx x₁ = idx x₂ := congrArg Prod.snd he
          have hf₁ := (is_fiber_iff_generates_quotient_point 𝔽q β i steps
            h_i_add_steps (x := x₁) (y := q x₁)).mp (by rfl)
          have hf₂ := (is_fiber_iff_generates_quotient_point 𝔽q β i steps
            h_i_add_steps (x := x₂) (y := q x₂)).mp (by rfl)
          rw [← hf₁, ← hf₂, hq, hk]
      _ = Y.ncard * 2 ^ steps := by
        simp only [Finset.card_product, Set.toFinset_card, Finset.card_univ,
          Fintype.card_fin]

  have h_dist_bridge : d_H ≤ d_fw * 2 ^ steps := by
    apply le_trans (b := hammingDist f g')
    · simp only [distFromCode, SetLike.mem_coe, hammingDist, d_H]
      apply sInf_le
      exact ⟨g', h_g'_mem, le_rfl⟩
    · exact h_dist_le

  have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 := by
    have h : 2 * d_fw < d_i_plus_steps :=
      WithTop.coe_lt_coe.mp h_fw_dist_lt
    omega

  have h_identity : (d_i_plus_steps - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_i_plus_steps, BBF_CodeDistance]
    rw [Nat.sub_mul, ← Nat.pow_add, ← Nat.pow_add]
    have h₁ : ℓ + 𝓡 - (i + steps) + steps = ℓ + 𝓡 - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel]
    have h₂ : ℓ - (i + steps) + steps = ℓ - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel]
    rw [h₁, h₂]

  have h_dH_ne_top : d_H ≠ ⊤ := by
    simp only [d_H]
    rw [Code.distFromCode_eq_top_iff_empty f C_i]
    exact Set.nonempty_iff_ne_empty'.mp h_C_i_nonempty

  let d_H_nat := ENat.toNat d_H
  have h_dH_eq : d_H = d_H_nat := (ENat.coe_toNat h_dH_ne_top).symm
  have h_final : 2 * d_H_nat ≤ d_i - 1 := by
    have h_bridge_nat : d_H_nat ≤ d_fw * 2 ^ steps := by
      rw [← ENat.coe_le_coe]
      exact le_of_eq_of_le h_dH_eq.symm h_dist_bridge
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