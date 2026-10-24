by
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let S := (fun (g : C_i) =>
    (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  rcases Nat.sInf_mem hS_nonempty with ⟨g_subtype, hg_subtype, hg_min⟩
  rcases g_subtype with ⟨g_closest, hg_mem⟩
  have h_fw_eq :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_i_add_steps f =
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g_closest).ncard := by
    change sInf S = _
    simpa using hg_min.symm

  let D := Finset.filter (fun x => f x ≠ g_closest x) Finset.univ
  let FW := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g_closest
  letI : Fintype FW := Fintype.ofFinite FW
  let E := FW.toFinset
  let q := fun x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ =>
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i) (k := steps)
      (h_bound := h_i_add_steps) x
  let k := fun x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ =>
    pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := h_i_add_steps) (x := x)
  let enc := fun x => (q x, k x)

  have h_card : D.card ≤ (E.product (Finset.univ : Finset (Fin (2 ^ steps)))).card := by
    apply Finset.card_le_card_of_injOn (f := enc)
    · intro x hx
      change q x ∈ E ∧ k x ∈ (Finset.univ : Finset (Fin (2 ^ steps)))
      constructor
      · simp only [E, Set.mem_toFinset]
        change ∃ z, q z = q x ∧ f z ≠ g_closest z
        exact ⟨x, rfl, (Finset.mem_filter.mp hx).2⟩
      · exact Finset.mem_univ _
    · intro x hx y hy hxy
      change (q x, k x) = (q y, k y) at hxy
      have hq : q x = q y := congrArg Prod.fst hxy
      have hk : k x = k y := congrArg Prod.snd hxy
      have hx_rec :=
        (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
          (x := x) (y := q x)).mp (by rfl)
      have hy_rec :=
        (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
          (x := y) (y := q y)).mp (by rfl)
      calc
        x = qMap_total_fiber 𝔽q β
            (i := ⟨i.val, fin_ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i⟩)
            (steps := steps)
            (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
            (y := q x) (k x) := hx_rec.symm
        _ = qMap_total_fiber 𝔽q β
            (i := ⟨i.val, fin_ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i⟩)
            (steps := steps)
            (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
            (y := q y) (k y) := by rw [hq, hk]
        _ = y := hy_rec

  have h_hamming_le :
      hammingDist f g_closest ≤
        2 ^ steps *
          (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps
            f g_closest).ncard := by
    simpa [D, E, FW, hammingDist, Nat.mul_comm] using h_card

  have h_dist_le_hamming :
      Code.distFromCode f
          (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) ≤
        (hammingDist f g_closest : ℕ∞) := by
    unfold Code.distFromCode
    apply sInf_le
    exact ⟨g_closest, hg_mem, le_rfl⟩

  have h_hamming_le_enat :
      (hammingDist f g_closest : ℕ∞) ≤
        ((2 ^ steps * fiberwiseDistance 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f : ℕ) : ℕ∞) := by
    exact_mod_cast h_hamming_le.trans_eq (congrArg (2 ^ steps * ·) h_fw_eq.symm)

  have h_fw_bound := h_fw_dist_lt
  unfold fiberwiseClose at h_fw_bound
  have h_fw_nat :
      2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f <
        BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ := by
    exact_mod_cast h_fw_bound

  have h_distance_identity :
      BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ =
        2 ^ steps * (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ - 1) + 1 := by
    have h_exp_top :
        ℓ + 𝓡 - i.val = steps + (ℓ + 𝓡 - (i.val + steps)) := by omega
    have h_exp_bottom :
        ℓ - i.val = steps + (ℓ - (i.val + steps)) := by omega
    unfold BBF_CodeDistance
    rw [h_exp_top, h_exp_bottom, Nat.pow_add, Nat.pow_add]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_sub_left_distrib]

  have h_fw_le :
      2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f ≤
        BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ - 1 := by
    omega
  have h_scaled := Nat.mul_le_mul_left (2 ^ steps) h_fw_le
  have h_numeric :
      2 * (2 ^ steps * fiberwiseDistance 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f) <
        BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ := by
    rw [h_distance_identity]
    calc
      2 * (2 ^ steps * fiberwiseDistance 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f) =
          2 ^ steps * (2 * fiberwiseDistance 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := i) steps h_i_add_steps f) := by ac_rfl
      _ ≤ 2 ^ steps * (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ - 1) := h_scaled
      _ < 2 ^ steps * (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ - 1) + 1 :=
        Nat.lt_succ_self _

  unfold hammingClose
  calc
    2 * Code.distFromCode f
        (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) ≤
      2 * (hammingDist f g_closest : ℕ∞) :=
        mul_le_mul_left' h_dist_le_hamming 2
    _ ≤ 2 * ((2 ^ steps * fiberwiseDistance 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_i_add_steps f : ℕ) : ℕ∞) :=
      mul_le_mul_left' h_hamming_le_enat 2
    _ < (BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ : ℕ∞) := by
      exact_mod_cast h_numeric