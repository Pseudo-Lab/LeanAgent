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
    omega

  have h_C_i_nonempty : Nonempty C_i := ⟨0⟩

  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw =
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').ncard := by
    let S := (fun (g : C_i) =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
    have hS : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have hm : sInf S ∈ S := Nat.sInf_mem hS
    unfold d_fw at hm
    rw [Set.mem_image] at hm
    rcases hm with ⟨g, _, hg⟩
    exact ⟨g, g.property, hg.symm⟩

  have h_dist_nat : hammingDist f g' ≤ d_fw * 2 ^ steps := by
    rw [h_g'_min_card]
    set Δ := Finset.filter (fun x => f x ≠ g' x) Finset.univ
    set Y := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g'
    change Δ.card ≤ Y.ncard * 2 ^ steps
    let Q := fun x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ =>
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
        (h_bound := h_i_add_steps) x
    let K := fun x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ =>
      pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (x := x)
    let e := fun x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ => (Q x, K x)
    calc
      Δ.card ≤ (Y.toFinset ×ˢ (Finset.univ : Finset (Fin (2 ^ steps)))).card := by
        apply Finset.card_le_card_of_injOn (f := e)
        · intro x hx
          simp only [e, Finset.mem_product, Set.mem_toFinset, Finset.mem_univ, and_true]
          change Q x ∈ Y
          change ∃ z, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
            (h_bound := h_i_add_steps) z = Q x ∧ f z ≠ g' z
          exact ⟨x, rfl, (Finset.mem_filter.mp hx).2⟩
        · intro x _ y _ hxy
          have hQ : Q x = Q y := congrArg Prod.fst hxy
          have hK : K x = K y := congrArg Prod.snd hxy
          have hxq :
              qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
                (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                (y := Q x) (K x) = x := by
            exact (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
              (x := x) (y := Q x)).mp rfl
          have hyq :
              qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
                (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                (y := Q y) (K y) = y := by
            exact (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
              (x := y) (y := Q y)).mp rfl
          calc
            x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
                (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                (y := Q x) (K x) := hxq.symm
            _ = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
                (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                (y := Q y) (K y) := by rw [hQ, hK]
            _ = y := hyq
      _ = Y.ncard * 2 ^ steps := by simp

  have h_dist_le_fw_dist_times_fiber_size :
      (hammingDist f g' : ℕ∞) ≤ d_fw * 2 ^ steps := by
    change (Δ₀(f, g') : ℕ∞) ≤ ↑d_fw * ((2 ^ steps : ℕ) : ℕ∞)
    rw [←ENat.coe_mul, ENat.coe_le_coe]
    exact h_dist_nat

  have h_dist_bridge : d_H ≤ d_fw * 2 ^ steps := by
    apply le_trans (b := hammingDist f g')
    · simp only [distFromCode, SetLike.mem_coe, hammingDist, ne_eq, d_H]
      apply sInf_le
      exact ⟨g', h_g'_mem, le_rfl⟩
    · exact h_dist_le_fw_dist_times_fiber_size

  have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 := by
    exact Nat.le_of_lt_succ (WithTop.coe_lt_coe.1 h_fw_dist_lt)

  have h_algebraic_identity :
      (d_i_plus_steps - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_i_plus_steps, BBF_CodeDistance]
    rw [Nat.sub_mul, ←Nat.pow_add, ←Nat.pow_add]
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

  have h_final_inequality : 2 * d_H_nat ≤ d_i - 1 := by
    have h_bridge_nat : d_H_nat ≤ d_fw * 2 ^ steps := by
      rw [←ENat.coe_le_coe]
      exact le_of_eq_of_le h_dH_eq.symm h_dist_bridge
    calc
      2 * d_H_nat ≤ 2 * (d_fw * 2 ^ steps) := by gcongr
      _ = (2 * d_fw) * 2 ^ steps := by rw [mul_assoc]
      _ ≤ (d_i_plus_steps - 1) * 2 ^ steps := by gcongr
      _ = d_i - 1 := h_algebraic_identity

  simp only [d_H, d_H_nat] at h_dH_eq
  rw [h_dH_eq]
  change ((2 : ℕ) : ℕ∞) * ↑Δ₀(f, C_i).toNat <
    ↑(BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩)
  rw [←ENat.coe_mul, ENat.coe_lt_coe]
  exact Nat.lt_of_le_pred h_d_i_gt_0 h_final_inequality