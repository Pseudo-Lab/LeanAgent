by
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let S := (fun (g : C_i) =>
    (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  rcases Nat.sInf_mem hS_nonempty with ⟨g, _, hg_min⟩
  let E := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f (g : _)
  have h_min : fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) steps h_i_add_steps f = E.ncard := by
    change sInf S = E.ncard
    simpa only [E] using hg_min.symm

  let Efin := E.toFinset
  let Dfin := Finset.univ.filter (fun x => f x ≠ (g : _) x)
  let encode (x : ↥Dfin) : (↥Efin) × Fin (2 ^ steps) := by
    let y := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := steps) (h_bound := h_i_add_steps) x.1
    let k := pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_i_add_steps := h_i_add_steps) (x := x.1)
    refine (⟨y, ?_⟩, k)
    change y ∈ E.toFinset
    rw [Set.mem_toFinset]
    change ∃ x', iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := steps) (h_bound := h_i_add_steps) x' = y ∧ f x' ≠ (g : _) x'
    refine ⟨x.1, rfl, ?_⟩
    simpa only [Dfin, Finset.mem_filter, Finset.mem_univ, true_and] using x.2
  have h_encode_injective : Function.Injective encode := by
    intro xa xb h
    let ya := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := steps) (h_bound := h_i_add_steps) xa.1
    let yb := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := steps) (h_bound := h_i_add_steps) xb.1
    let ka := pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_i_add_steps := h_i_add_steps) (x := xa.1)
    let kb := pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_i_add_steps := h_i_add_steps) (x := xb.1)
    have hy : ya = yb := by
      have hh := congrArg (fun z => z.1.val) h
      simpa only [encode, ya, yb] using hh
    have hk : ka = kb := by
      have hh := congrArg Prod.snd h
      simpa only [encode, ka, kb] using hh
    have hxa := (is_fiber_iff_generates_quotient_point 𝔽q β i steps
      h_i_add_steps (x := xa.1) (y := ya)).mp (by rfl)
    have hxb := (is_fiber_iff_generates_quotient_point 𝔽q β i steps
      h_i_add_steps (x := xb.1) (y := yb)).mp (by rfl)
    apply Subtype.ext
    calc
      xa.1 = _ := hxa.symm
      _ = _ := by rw [hy, hk]
      _ = xb.1 := hxb
  have h_card : Dfin.card ≤ Efin.card * 2 ^ steps := by
    simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using
      (Fintype.card_le_of_injective encode h_encode_injective)
  have h_hamming_le : hammingDist f (g : _) ≤ E.ncard * 2 ^ steps := by
    change Dfin.card ≤ E.ncard * 2 ^ steps
    rw [Set.ncard_eq_toFinset_card]
    simpa only [Efin] using h_card

  have h_dist_le :
      Code.distFromCode (u := f) (C := C_i) ≤ (hammingDist f (g : _) : ℕ∞) := by
    unfold Code.distFromCode
    apply sInf_le
    refine ⟨(g : _), g.property, ?_⟩
    exact le_rfl
  have h_fw_nat :
      2 * E.ncard < BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ := by
    unfold fiberwiseClose at h_fw_dist_lt
    rw [h_min] at h_fw_dist_lt
    exact_mod_cast h_fw_dist_lt

  have h_distance_scale :
      BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ =
        2 ^ steps * (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ - 1) + 1 := by
    unfold BBF_CodeDistance
    have h₁ : ℓ + 𝓡 - i.val = (ℓ + 𝓡 - (i.val + steps)) + steps := by omega
    have h₂ : ℓ - i.val = (ℓ - (i.val + steps)) + steps := by omega
    rw [h₁, h₂, pow_add, pow_add]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_sub_left_distrib]
    simp only [Nat.mul_comm]
  have h_hamming_scaled :
      2 * hammingDist f (g : _) ≤ 2 ^ steps * (2 * E.ncard) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (Nat.mul_le_mul_left 2 h_hamming_le)
  have h_scaled_lt :
      2 ^ steps * (2 * E.ncard) < BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ := by
    rw [h_distance_scale]
    have hpred :
        2 * E.ncard ≤ BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ - 1 := by
      omega
    exact Nat.lt_succ_of_le (Nat.mul_le_mul_left (2 ^ steps) hpred)

  unfold hammingClose
  change 2 * Code.distFromCode (u := f) (C := C_i) <
    (BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ : ℕ∞)
  calc
    2 * Code.distFromCode (u := f) (C := C_i)
        ≤ 2 * (hammingDist f (g : _) : ℕ∞) := mul_le_mul_left' h_dist_le 2
    _ ≤ ((2 ^ steps * (2 * E.ncard) : ℕ) : ℕ∞) := by
      exact_mod_cast h_hamming_scaled
    _ < (BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ : ℕ∞) := by
      exact_mod_cast h_scaled_lt