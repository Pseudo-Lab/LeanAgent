theorem fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius (i : Fin ℓ) (steps : ℕ)
    [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps) (f := f)) :
  hammingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ f := by
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').ncard := by
    obtain ⟨g, _, h_eq⟩ := Nat.sInf_mem (Set.univ_nonempty.image fun (g : C_i) =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard)
    exact ⟨g, g.2, h_eq.symm⟩
  have hΔ : hammingDist f g' ≤ d_fw * 2 ^ steps := by
    rw [h_g'_min_card]
    have := Fintype.ofFinite (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g')
    refine (Finset.card_le_card (t := (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f
      g').toFinset.biUnion fun y => ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := lt_add_of_pos_right_of_le _ _ _ h_i_add_steps) (y := y)) ''
          (Finset.univ : Finset (Fin (2 ^ steps)))).toFinset) fun x hx => Finset.mem_biUnion.2
        ⟨iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x, ?_, ?_⟩).trans
      ((Finset.card_biUnion_le_card_mul _ _ (2 ^ steps) fun y _ => ?_).trans ?_)
    · simp only [fiberwiseDisagreementSet, iteratedQuotientMap, ne_eq, Subtype.exists,
        Set.toFinset_setOf, mem_filter, mem_univ, true_and]
      exact ⟨x.val, x.2, rfl, by simpa using hx⟩
    · simp only [coe_univ, Set.image_univ, Set.toFinset_range, mem_image, mem_univ, true_and]
      exact ⟨_, (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps x _).mp rfl⟩
    · simp only [coe_univ, Set.image_univ, Set.toFinset_range]
      exact Finset.card_image_le.trans_eq (Finset.card_univ.trans (Fintype.card_fin _))
    · rw [Set.ncard_eq_toFinset_card']
  have h3 := Nat.mul_le_mul_right (2 ^ steps) (Nat.le_of_lt_succ (WithTop.coe_lt_coe.1 h_fw_dist_lt) :
    2 * d_fw ≤ BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ - 1)
  simp only [BBF_CodeDistance, Nat.add_sub_cancel, Nat.sub_mul, ← Nat.pow_add, Nat.mul_assoc,
    show ℓ + 𝓡 - (↑i + steps) + steps = ℓ + 𝓡 - i by omega,
    show ℓ - (↑i + steps) + steps = ℓ - i by omega] at h3
  exact (mul_le_mul_left' (le_trans (sInf_le ⟨g', h_g'_mem, le_rfl⟩) (ENat.coe_le_coe.2 hΔ) :
    Code.distFromCode f C_i ≤ _) 2).trans_lt (mod_cast (show 2 * (d_fw * 2 ^ steps) <
      BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ by simp only [BBF_CodeDistance]; omega))