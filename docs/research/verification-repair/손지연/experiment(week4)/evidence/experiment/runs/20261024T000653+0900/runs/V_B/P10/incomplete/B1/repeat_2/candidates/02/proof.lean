by
  classical
  unfold fiberwiseClose at h_fw_dist_lt
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let S : Set ℕ :=
    (fun (g : C_i) =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  rcases Nat.sInf_mem hS_nonempty with ⟨g, _, hg⟩
  let FW := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g
  have h_fiber_dist_eq :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_i_add_steps f = FW.ncard := by
    change sInf S = FW.ncard
    exact hg.symm
  let D := Finset.filter (fun x => f x ≠ g.val x) Finset.univ
  let q := fun x =>
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := steps) (h_bound := h_i_add_steps) x
  let k := fun
      (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩) =>
    pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := h_i_add_steps) (x := x)
  let encode := fun x => (q x, k x)
  have h_card :
      D.card ≤
        (FW.toFinset ×ˢ (Finset.univ : Finset (Fin (2 ^ steps)))).card := by
    apply Finset.card_le_card_of_injOn (f := encode)
    · intro x hx
      have hx_ne : f x ≠ g.val x := (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_product, Set.mem_toFinset, Finset.mem_univ, and_true]
      change ∃ x', q x' = q x ∧ f x' ≠ g.val x'
      exact ⟨x, rfl, hx_ne⟩
    · intro x _ z _ hxz
      have hq : q x = q z := congrArg Prod.fst hxz
      have hk : k x = k z := congrArg Prod.snd hxz
      have hx_reconstruct :
          qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
            (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
            (y := q x) (k x) = x := by
        exact
          (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
            (x := x) (y := q x)).mp rfl
      have hz_reconstruct :
          qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
            (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
            (y := q z) (k z) = z := by
        exact
          (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
            (x := z) (y := q z)).mp rfl
      calc
        x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
              (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
              (y := q x) (k x) := hx_reconstruct.symm
        _ = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
              (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
              (y := q z) (k z) := by rw [hq, hk]
        _ = z := hz_reconstruct
  have h_hamming_le_fw :
      hammingDist f g.val ≤
        2 ^ steps * fiberwiseDistance 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f := by
    have hD : D.card ≤ 2 ^ steps * FW.ncard := by
      calc
        D.card ≤
            (FW.toFinset ×ˢ (Finset.univ : Finset (Fin (2 ^ steps)))).card := h_card
        _ = FW.toFinset.card * 2 ^ steps := by simp
        _ = 2 ^ steps * FW.ncard := by
          rw [Nat.mul_comm, Set.ncard_eq_toFinset_card]
    rw [h_fiber_dist_eq]
    exact hD
  have h_dist_le_hamming :
      Code.distFromCode f
          (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) ≤
        (hammingDist f g.val : ℕ∞) := by
    change Code.distFromCode f C_i ≤ (hammingDist f g.val : ℕ∞)
    unfold Code.distFromCode
    apply sInf_le
    exact ⟨g.val, g.property, le_rfl⟩
  have h_fw_nat :
      2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f <
        BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ := by
    apply ENat.coe_lt_coe.mp
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h_fw_dist_lt
  simp only [BBF_CodeDistance, Fin.val_mk] at h_fw_nat
  have h_fw_le :
      2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f ≤
        2 ^ (ℓ + 𝓡 - (i.val + steps)) - 2 ^ (ℓ - (i.val + steps)) := by
    omega
  have h_code_distance_eq :
      BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ =
        2 ^ steps *
            (2 ^ (ℓ + 𝓡 - (i.val + steps)) - 2 ^ (ℓ - (i.val + steps))) + 1 := by
    simp only [BBF_CodeDistance, Fin.val_mk]
    rw [show ℓ + 𝓡 - i.val = steps + (ℓ + 𝓡 - (i.val + steps)) by omega]
    rw [show ℓ - i.val = steps + (ℓ - (i.val + steps)) by omega]
    rw [pow_add, pow_add, Nat.mul_sub_left_distrib]
  have h_scaled_lt :
      2 *
          (2 ^ steps *
            fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := i) steps h_i_add_steps f) <
        BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ := by
    rw [h_code_distance_eq]
    calc
      2 *
          (2 ^ steps *
            fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := i) steps h_i_add_steps f) =
          2 ^ steps *
            (2 * fiberwiseDistance 𝔽q β
              (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := i) steps h_i_add_steps f) := by ring
      _ ≤ 2 ^ steps *
          (2 ^ (ℓ + 𝓡 - (i.val + steps)) - 2 ^ (ℓ - (i.val + steps))) :=
        Nat.mul_le_mul_left _ h_fw_le
      _ < 2 ^ steps *
          (2 ^ (ℓ + 𝓡 - (i.val + steps)) - 2 ^ (ℓ - (i.val + steps))) + 1 :=
        Nat.lt_succ_self _
  unfold hammingClose
  calc
    2 * Code.distFromCode f
        (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) ≤
        2 * (hammingDist f g.val : ℕ∞) :=
      mul_le_mul_left' h_dist_le_hamming 2
    _ ≤ 2 *
        (2 ^ steps * fiberwiseDistance 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f : ℕ) := by
      apply mul_le_mul_left'
      exact ENat.coe_le_coe.mpr h_hamming_le_fw
    _ < (BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ : ℕ∞) := by
      exact ENat.coe_lt_coe.mpr h_scaled_lt