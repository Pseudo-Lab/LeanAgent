by
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val, by omega⟩
  let fwSet (g : C_i) :=
    fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f (g : _)
  let S := (fun g : C_i => (fwSet g).ncard) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  rcases Nat.sInf_mem hS_nonempty with ⟨g, _, hg_min⟩
  have h_fiberwiseDistance :
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f = sInf S := by
    rfl
  have hg_min' :
      (fwSet g).ncard =
        fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f := by
    rw [h_fiberwiseDistance]
    exact hg_min

  let quotient := fun x =>
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := steps) (h_bound := h_i_add_steps) x
  let index := fun
      (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) =>
    pointToIterateQuotientIndex
      (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := h_i_add_steps) (x := x)
  let fiber := fun
      (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps, by omega⟩)
      (k : Fin (2 ^ steps)) =>
    qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      (y := y) k
  let D := Finset.filter (fun x => f x ≠ (g : _) x) Finset.univ
  let FW := (fwSet g).toFinset
  let encode : ↥D → ↥FW × Fin (2 ^ steps) := fun x =>
    (⟨quotient x, by
      rw [Set.mem_toFinset]
      change ∃ z, quotient z = quotient x ∧ f z ≠ (g : _) z
      exact ⟨x, rfl, by simpa [D] using x.property⟩⟩,
      index x)
  have h_reconstruct (x : ↥D) :
      fiber (quotient x) (index x) = (x : _) := by
    have hx :=
      (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
        (x := (x : _)) (y := quotient x)).mp (by rfl)
    simpa [fiber, quotient, index] using hx
  have h_encode_injective : Function.Injective encode := by
    intro x₁ x₂ h
    have hy₀ : (encode x₁).1 = (encode x₂).1 :=
      congrArg (fun z => z.1) h
    have hy : quotient x₁ = quotient x₂ :=
      congrArg Subtype.val hy₀
    have hk : index x₁ = index x₂ :=
      congrArg (fun z => z.2) h
    apply Subtype.ext
    calc
      (x₁ : _) = fiber (quotient x₁) (index x₁) := (h_reconstruct x₁).symm
      _ = fiber (quotient x₂) (index x₂) := by rw [hy, hk]
      _ = (x₂ : _) := h_reconstruct x₂
  have h_card := Fintype.card_le_of_injective encode h_encode_injective
  have h_card' : D.card ≤ FW.card * 2 ^ steps := by
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using h_card
  have h_hamming_le :
      hammingDist f (g : _) ≤ 2 ^ steps * (fwSet g).ncard := by
    change D.card ≤ 2 ^ steps * (fwSet g).ncard
    rw [Set.ncard_eq_toFinset_card]
    simpa [FW, Nat.mul_comm] using h_card'

  have h_dist_le :
      Code.distFromCode (u := f) (C := C_i) ≤
        (hammingDist f (g : _) : ℕ∞) := by
    simp only [Code.distFromCode]
    apply sInf_le
    use g
    simp only [Fin.eta, Subtype.coe_prop, le_refl, and_self]

  have h_fw_nat :
      2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_i_add_steps f <
        BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ := by
    unfold fiberwiseClose at h_fw_dist_lt
    exact_mod_cast h_fw_dist_lt
  have h_fw_le :
      2 * (fwSet g).ncard ≤
        BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ - 1 := by
    rw [hg_min']
    omega

  have h_domain_exp :
      ℓ + 𝓡 - i.val = steps + (ℓ + 𝓡 - (i.val + steps)) := by
    omega
  have h_degree_exp :
      ℓ - i.val = steps + (ℓ - (i.val + steps)) := by
    omega
  have h_distance_formula :
      BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ =
        2 ^ steps *
          (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ - 1) + 1 := by
    unfold BBF_CodeDistance
    simp only [Fin.val_mk]
    rw [h_domain_exp, h_degree_exp, pow_add, pow_add]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_sub_left_distrib]

  have h_hamming_nat :
      2 * hammingDist f (g : _) <
        BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ := by
    calc
      2 * hammingDist f (g : _)
          ≤ 2 * (2 ^ steps * (fwSet g).ncard) :=
        Nat.mul_le_mul_left 2 h_hamming_le
      _ = 2 ^ steps * (2 * (fwSet g).ncard) := by ac_rfl
      _ ≤ 2 ^ steps *
          (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ - 1) :=
        Nat.mul_le_mul_left (2 ^ steps) h_fw_le
      _ < BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ := by
        rw [h_distance_formula]
        omega

  unfold hammingClose
  change 2 * Code.distFromCode (u := f) (C := C_i) <
    (BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ : ℕ∞)
  calc
    2 * Code.distFromCode (u := f) (C := C_i)
        ≤ 2 * (hammingDist f (g : _) : ℕ∞) :=
      mul_le_mul_left' h_dist_le 2
    _ < (BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩ : ℕ∞) := by
      exact_mod_cast h_hamming_nat