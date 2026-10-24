by
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let δ := fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) steps h_i_add_steps f
  let S : Set ℕ := (fun (g : C_i) =>
    (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g.1).ncard) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  rcases Nat.sInf_mem hS_nonempty with ⟨g, _, hg_min⟩
  let D := Finset.filter (fun x => f x ≠ g.1 x) Finset.univ
  let FW := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g.1
  letI : Fintype {y // y ∈ FW} := Fintype.ofFinite _
  let Y := FW.toFinset
  let q := fun x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ =>
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
      (h_bound := h_i_add_steps) x
  let idx := fun x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ =>
    pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := h_i_add_steps) (x := x)
  let back := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
  have recover
      (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩) :
      back (q x) (idx x) = x := by
    dsimp only [back, q, idx]
    exact (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
      (x := x)
      (y := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
        (h_bound := h_i_add_steps) x)).mp rfl
  let e : {x // x ∈ D} → {y // y ∈ Y} × Fin (2 ^ steps) := fun x =>
    (⟨q x, by
      change q x ∈ FW.toFinset
      rw [Set.mem_toFinset]
      change ∃ z, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
        (h_bound := h_i_add_steps) z = q x ∧ f z ≠ g.1 z
      have hx : f x ≠ g.1 x := (Finset.mem_filter.mp x.property).2
      exact ⟨x, rfl, hx⟩⟩, idx x)
  have he_injective : Function.Injective e := by
    intro x₁ x₂ heq
    have hq : q x₁ = q x₂ := congrArg (fun z => (z.1).val) heq
    have hk : idx x₁ = idx x₂ := congrArg Prod.snd heq
    apply Subtype.ext
    calc
      (x₁ : _) = back (q x₁) (idx x₁) := (recover x₁).symm
      _ = back (q x₂) (idx x₂) := congrArg₂ back hq hk
      _ = (x₂ : _) := recover x₂
  have h_card : D.card ≤ Y.card * 2 ^ steps := by
    have h := Fintype.card_le_of_injective e he_injective
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] using h
  have hY_card : Y.card = FW.ncard := by
    simp only [Y, Set.ncard_eq_toFinset_card]
  have hg_min' : FW.ncard = δ := by
    simpa only [FW, fiberwiseDistance, C_i, S, δ] using hg_min
  have h_hamming : hammingDist f g.1 ≤ 2 ^ steps * δ := by
    have hD : hammingDist f g.1 = D.card := by rfl
    rw [hD]
    calc
      D.card ≤ Y.card * 2 ^ steps := h_card
      _ = 2 ^ steps * δ := by rw [hY_card, hg_min', Nat.mul_comm]
  have h_dist_le :
      Code.distFromCode (u := f) (C := C_i) ≤
        (hammingDist f g.1 : ℕ∞) := by
    unfold Code.distFromCode
    apply sInf_le
    exact ⟨g.1, g.2, le_rfl⟩
  let dnext := BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩
  let di := BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩
  have h_fw_enat : (2 : ℕ∞) * (δ : ℕ∞) < (dnext : ℕ∞) := by
    simpa only [fiberwiseClose, δ, dnext] using h_fw_dist_lt
  have h_fw_nat : 2 * δ < dnext := by
    apply ENat.coe_lt_coe.mp
    simpa using h_fw_enat
  have h_pow₁ :
      2 ^ (ℓ + 𝓡 - i.val) =
        2 ^ steps * 2 ^ (ℓ + 𝓡 - (i.val + steps)) := by
    rw [← pow_add]
    congr 1
    omega
  have h_pow₂ :
      2 ^ (ℓ - i.val) = 2 ^ steps * 2 ^ (ℓ - (i.val + steps)) := by
    rw [← pow_add]
    congr 1
    omega
  have h_distance_identity : di = 2 ^ steps * (dnext - 1) + 1 := by
    simp only [di, dnext, BBF_CodeDistance, Fin.coe_mk]
    rw [h_pow₁, h_pow₂]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_sub_left_distrib]
  have hle : 2 * δ ≤ dnext - 1 := by omega
  have h_num : 2 * (2 ^ steps * δ) < di := by
    calc
      2 * (2 ^ steps * δ) = 2 ^ steps * (2 * δ) := by ac_rfl
      _ ≤ 2 ^ steps * (dnext - 1) := Nat.mul_le_mul_left _ hle
      _ < 2 ^ steps * (dnext - 1) + 1 := Nat.lt_succ_self _
      _ = di := h_distance_identity.symm
  have h_num_enat :
      (2 : ℕ∞) * ((2 ^ steps * δ : ℕ) : ℕ∞) < (di : ℕ∞) := by
    have h := ENat.coe_lt_coe.mpr h_num
    simpa using h
  have h_hamming_enat :
      (hammingDist f g.1 : ℕ∞) ≤ ((2 ^ steps * δ : ℕ) : ℕ∞) :=
    ENat.coe_le_coe.mpr h_hamming
  unfold hammingClose
  change 2 * Code.distFromCode (u := f) (C := C_i) < (di : ℕ∞)
  calc
    2 * Code.distFromCode (u := f) (C := C_i) ≤
        2 * (hammingDist f g.1 : ℕ∞) := mul_le_mul_left' h_dist_le 2
    _ ≤ 2 * ((2 ^ steps * δ : ℕ) : ℕ∞) := mul_le_mul_left' h_hamming_enat 2
    _ < (di : ℕ∞) := h_num_enat