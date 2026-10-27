by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩

  obtain ⟨g, hg, hmin⟩ : ∃ g ∈ C_i,
      d_fw = (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard := by
    let S := (fun g : C_i =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
    have hm : sInf S ∈ S := Nat.sInf_mem (Set.image_nonempty.mpr Set.univ_nonempty)
    rcases hm with ⟨g, _, hgmin⟩
    have hd : d_fw = sInf S := rfl
    exact ⟨g, g.property, hd.trans hgmin.symm⟩

  have h_hamming_le : hammingDist f g ≤ d_fw * 2 ^ steps := by
    rw [hmin]
    let ΔH := Finset.filter (fun x => f x ≠ g x) Finset.univ
    let Y := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g
    have hdist : hammingDist f g = ΔH.card := by simp [ΔH, hammingDist]
    rw [hdist]
    change ΔH.card ≤ Y.ncard * 2 ^ steps
    let q := fun x : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ =>
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x
    let idx := fun x : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ =>
      pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (x := x)
    let pair := fun x => (q x, idx x)
    let T := Y.toFinset ×ˢ (Finset.univ : Finset (Fin (2 ^ steps)))
    have recover (x : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨i, by omega⟩) :
        qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
          (y := q x) (idx x) = x := by
      exact (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
        (x := x) (y := q x)).mp rfl
    have hmap : Set.MapsTo pair (↑ΔH) (↑T) := by
      intro x hx
      have hbad : f x ≠ g x := by
        simpa [ΔH] using (Finset.mem_filter.mp hx).2
      have hqy : q x ∈ Y := by
        change ∃ z, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps
          h_i_add_steps z = q x ∧ f z ≠ g z
        exact ⟨x, rfl, hbad⟩
      change pair x ∈ T
      simp [T, pair, hqy]
    have hinj : Set.InjOn pair (↑ΔH) := by
      intro x _ z _ heq
      have hq := congrArg Prod.fst heq
      have hk := congrArg Prod.snd heq
      simp only [pair] at hq hk
      rw [← recover x, ← recover z, hq, hk]
    calc
      ΔH.card ≤ T.card := Finset.card_le_card_of_injOn (f := pair) hmap hinj
      _ = Y.ncard * 2 ^ steps := by simp [T]

  have h_dist_g : (hammingDist f g : ℕ∞) ≤
      ((d_fw * 2 ^ steps : ℕ) : ℕ∞) := ENat.coe_le_coe.mpr h_hamming_le
  have h_dist_bridge : d_H ≤ ((d_fw * 2 ^ steps : ℕ) : ℕ∞) := by
    apply le_trans (b := (hammingDist f g : ℕ∞))
    · simp only [distFromCode, SetLike.mem_coe, hammingDist, ne_eq, d_H]
      apply sInf_le
      exact ⟨g, hg, le_rfl⟩
    · exact h_dist_g

  have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 := by
    have h : 2 * d_fw < d_i_plus_steps := WithTop.coe_lt_coe.1 h_fw_dist_lt
    omega

  have h_algebraic_identity :
      (d_i_plus_steps - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_i_plus_steps, BBF_CodeDistance]
    rw [Nat.sub_mul, ← Nat.pow_add, ← Nat.pow_add]
    have h1 : ℓ + 𝓡 - (i + steps) + steps = ℓ + 𝓡 - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel]
    have h2 : ℓ - (i + steps) + steps = ℓ - i := by
      rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega),
        Nat.add_sub_cancel]
    rw [h1, h2]

  have h_d_i_pos : 0 < d_i := by simp [d_i, BBF_CodeDistance]
  change 2 * d_H < (d_i : ℕ∞)
  calc
    2 * d_H ≤ 2 * ((d_fw * 2 ^ steps : ℕ) : ℕ∞) :=
      mul_le_mul_left' h_dist_bridge 2
    _ = (((2 * d_fw) * 2 ^ steps : ℕ) : ℕ∞) := by
      simp only [cast_mul, cast_ofNat]
      rw [mul_assoc]
    _ ≤ (((d_i_plus_steps - 1) * 2 ^ steps : ℕ) : ℕ∞) :=
      ENat.coe_le_coe.mpr (Nat.mul_le_mul_right _ h_fw_bound)
    _ = ((d_i - 1 : ℕ) : ℕ∞) :=
      congrArg (fun n : ℕ => (n : ℕ∞)) h_algebraic_identity
    _ < (d_i : ℕ∞) := ENat.coe_lt_coe.mpr (by omega)