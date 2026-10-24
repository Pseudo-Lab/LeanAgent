by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i.val + steps, by omega⟩
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw =
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').ncard := by
    let S := (fun g : C_i =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
    have hS : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have h := Nat.sInf_mem hS
    rw [Set.mem_image] at h
    rcases h with ⟨g, _, hg⟩
    exact ⟨g.val, g.property, hg.symm⟩
  have h_dist_le : (hammingDist f g' : ℕ∞) ≤ d_fw * 2 ^ steps := by
    change (Δ₀(f, g') : ℕ∞) ≤ ↑d_fw * ((2 ^ steps : ℕ) : ℕ∞)
    rw [← ENat.coe_mul, ENat.coe_le_coe, h_g'_min_card]
    set ΔH := Finset.filter (fun x => f x ≠ g' x) Finset.univ
    have h_dist_eq : hammingDist f g' = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [h_dist_eq]
    set Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g'
    simp only at *
    have hY : Fintype Y_bad := Fintype.ofFinite Y_bad
    have hsub : ΔH ⊆ Finset.biUnion Y_bad.toFinset (fun y =>
        ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y) ''
          (Finset.univ : Finset (Fin (2 ^ steps)))).toFinset) := by
      intro x hx
      simp only [ΔH, Finset.mem_filter] at hx
      let y := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x
      apply Finset.mem_biUnion.mpr
      use y
      have hy : y ∈ Y_bad.toFinset := by
        simp only [fiberwiseDisagreementSet, iteratedQuotientMap, ne_eq, Subtype.exists,
          Set.toFinset_setOf, mem_filter, mem_univ, true_and, Y_bad]
        let X := x.val
        use X, Submodule.coe_mem x
        have hmap : Polynomial.eval X
            (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩
              ⟨steps, by simp only; omega⟩) = y := by
          simp only [iteratedQuotientMap, X, y]
        have hne : f ⟨X, by omega⟩ ≠ g' ⟨X, by omega⟩ := by
          unfold X
          simpa only [Subtype.coe_eta, ne_eq] using hx.2
        simp only [hmap, Subtype.coe_eta, hne, not_false_eq_true, and_self]
      refine ⟨hy, ?_⟩
      simp only [coe_univ, Set.image_univ, Set.toFinset_range, mem_image, mem_univ,
        true_and]
      use pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (x := x)
      exact (is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y)).mp rfl
    apply (Finset.card_le_card hsub).trans
    rw [Finset.card_biUnion]
    · simp only [Set.toFinset_card]
      have hc := card_qMap_total_fiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
      simp only [Set.image_univ, Fintype.card_ofFinset, Subtype.forall] at hc
      have heach : ∀ y ∈ Y_bad.toFinset,
          Fintype.card ((qMap_total_fiber 𝔽q β (i := ⟨↑i, by omega⟩)
            (steps := steps)
            (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y) ''
            ↑(Finset.univ : Finset (Fin (2 ^ steps)))) = 2 ^ steps := by
        intro y _
        have := hc (a := y) (b := Submodule.coe_mem y)
        simpa only [coe_univ, Set.image_univ, Fintype.card_ofFinset] using this
      rw [Finset.sum_congr rfl heach]
      simp only [sum_const, Set.toFinset_card, smul_eq_mul, ge_iff_le]
      conv_rhs => rw [← _root_.Nat.card_coe_set_eq]
      simp only [card_eq_fintype_card, le_refl]
    · intro y₁ _ y₂ _ hne
      exact qMap_total_fiber_disjoint (i := ⟨↑i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (y₁ := y₁) (y₂ := y₂) hne
  have h_bridge : d_H ≤ d_fw * 2 ^ steps := by
    apply le_trans (b := hammingDist f g')
    · simp only [distFromCode, SetLike.mem_coe, hammingDist, ne_eq, d_H]
      apply sInf_le
      use g'
    · exact h_dist_le
  have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 :=
    Nat.le_of_lt_succ (WithTop.coe_lt_coe.1 h_fw_dist_lt)
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