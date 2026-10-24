by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw =
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').ncard := by
    let S := (fun g : C_i =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
    have hS : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    obtain ⟨g, _, hg⟩ := (Set.mem_image _ _ _).mp (Nat.sInf_mem hS)
    exact ⟨g, g.property, hg.symm⟩
  have h_dist_le : (hammingDist f g' : ℕ∞) ≤ d_fw * 2 ^ steps := by
    set ΔH := Finset.filter (fun x => f x ≠ g' x) Finset.univ
    set Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g'
    letI : Fintype Y_bad := Fintype.ofFinite Y_bad
    let q (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩) :=
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x
    let idx (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩) :=
      pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) x
    let B := ↥ΔH
    let encode (x : B) : Y_bad × Fin (2 ^ steps) :=
      (⟨q x, by
        have hx : f x ≠ g' x := by
          simpa only [ΔH, Finset.mem_filter, mem_univ, true_and] using x.property
        exact ⟨x, rfl, hx⟩⟩, idx x)
    have hencode : Function.Injective encode := by
      intro x₁ x₂ he
      have hq := congrArg Subtype.val (congrArg Prod.fst he)
      change q x₁ = q x₂ at hq
      have hk := congrArg Prod.snd he
      change idx x₁ = idx x₂ at hk
      have hx₁ :
          qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
            (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
            (q x₁) (idx x₁) = x₁.val := by
        exact (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
          (x := x₁.val) (y := q x₁)).mp rfl
      have hx₂ :
          qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
            (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
            (q x₂) (idx x₂) = x₂.val := by
        exact (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
          (x := x₂.val) (y := q x₂)).mp rfl
      apply Subtype.ext
      calc
        x₁.val = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
            (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
            (q x₁) (idx x₁) := hx₁.symm
        _ = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
            (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
            (q x₂) (idx x₂) := by rw [hq, hk]
        _ = x₂.val := hx₂
    have hc := Fintype.card_le_of_injective encode hencode
    have hYcard : Fintype.card Y_bad = Y_bad.ncard := by
      rw [← _root_.Nat.card_coe_set_eq, card_eq_fintype_card]
    have hnat : ΔH.card ≤ Y_bad.ncard * 2 ^ steps := by
      simpa only [B, Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
        hYcard] using hc
    change (↑(hammingDist f g') : ℕ∞) ≤ ↑(d_fw * 2 ^ steps)
    apply ENat.coe_le_coe.mpr
    rw [show hammingDist f g' = ΔH.card by simp only [hammingDist, ΔH],
      ← h_g'_min_card]
    exact hnat
  have h_bridge : d_H ≤ d_fw * 2 ^ steps := by
    apply le_trans (b := hammingDist f g')
    · simp only [distFromCode, SetLike.mem_coe, hammingDist, ne_eq, d_H]
      apply sInf_le
      exact ⟨g', h_g'_mem, le_rfl⟩
    · exact h_dist_le
  have h_fw_nat : 2 * d_fw < d_i_plus_steps :=
    WithTop.coe_lt_coe.1 h_fw_dist_lt
  have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 := by omega
  have h_identity : (d_i_plus_steps - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_i_plus_steps, BBF_CodeDistance]
    rw [Nat.sub_mul, ← Nat.pow_add, ← Nat.pow_add]
    have h1 : ℓ + 𝓡 - (↑i + steps) + steps = ℓ + 𝓡 - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel]
    have h2 : ℓ - (↑i + steps) + steps = ℓ - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel]
    rw [h1, h2]
  have hdi : 0 < d_i := by
    dsimp [d_i, BBF_CodeDistance]
    omega
  change 2 * d_H < (d_i : ℕ∞)
  calc
    2 * d_H ≤ 2 * (d_fw * 2 ^ steps) := mul_le_mul_left' h_bridge 2
    _ = (((2 * d_fw) * 2 ^ steps : ℕ) : ℕ∞) := by
      simp only [ENat.coe_mul]
      rw [mul_assoc]
    _ ≤ (((d_i_plus_steps - 1) * 2 ^ steps : ℕ) : ℕ∞) :=
      ENat.coe_le_coe.mpr (Nat.mul_le_mul_right _ h_fw_bound)
    _ = ((d_i - 1 : ℕ) : ℕ∞) := congrArg (fun n : ℕ => (n : ℕ∞)) h_identity
    _ < (d_i : ℕ∞) := ENat.coe_lt_coe.mpr (by omega)