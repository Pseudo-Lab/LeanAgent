by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩
  let d_next := BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩
  have hdpos : 0 < d_i := by
    dsimp [d_i, BBF_CodeDistance]
    omega
  have hC : Nonempty C_i := by
    simp only [nonempty_subtype, C_i]
    exact Submodule.nonempty _
  obtain ⟨g, hg, hmin⟩ : ∃ g ∈ C_i, d_fw =
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard := by
    let S := (fun g : C_i =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
    have hm : sInf S ∈ S := Nat.sInf_mem (Set.image_nonempty.mpr Set.univ_nonempty)
    rcases hm with ⟨g, _, h⟩
    exact ⟨g, g.property, h.symm⟩
  have hfg_nat : hammingDist f g ≤ d_fw * 2 ^ steps := by
    rw [hmin]
    set Δ := Finset.filter (fun x => f x ≠ g x) Finset.univ
    set Y := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g
    let Q := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
      (k := steps) (h_bound := h_i_add_steps)
    let K := fun x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ =>
      pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (x := x)
    let F := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega)
    let e : {x // x ∈ Δ} → {y // y ∈ Y.toFinset} × Fin (2 ^ steps) := fun x =>
      (⟨Q x, by
        rw [Set.mem_toFinset]
        change ∃ z, Q z = Q x ∧ f z ≠ g z
        exact ⟨x, rfl, (Finset.mem_filter.mp x.property).2⟩⟩, K x)
    have he : Function.Injective e := by
      intro x x' h
      have hQ : Q x = Q x' := by
        simpa only [e] using congrArg (fun z => (z.1).val) h
      have hK : K x = K x' := by
        simpa only [e] using congrArg Prod.snd h
      apply Subtype.ext
      have hx : F (Q x) (K x) = x :=
        (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
          (x := x) (y := Q x)).mp rfl
      have hx' : F (Q x') (K x') = x' :=
        (is_fiber_iff_generates_quotient_point 𝔽q β i steps h_i_add_steps
          (x := x') (y := Q x')).mp rfl
      rw [← hx, ← hx', hQ, hK]
    change Δ.card ≤ Y.ncard * 2 ^ steps
    calc
      Δ.card = Fintype.card {x // x ∈ Δ} := by simp
      _ ≤ Fintype.card ({y // y ∈ Y.toFinset} × Fin (2 ^ steps)) :=
        Fintype.card_le_of_injective e he
      _ = Y.ncard * 2 ^ steps := by simp
  have hfg : (hammingDist f g : ℕ∞) ≤ d_fw * 2 ^ steps := by
    simpa using (ENat.coe_le_coe.mpr hfg_nat)
  have hbridge : d_H ≤ d_fw * 2 ^ steps := by
    apply le_trans (b := (hammingDist f g : ℕ∞))
    · simp only [distFromCode, SetLike.mem_coe, hammingDist, ne_eq, d_H]
      apply sInf_le
      exact ⟨g, hg, le_rfl⟩
    · exact hfg
  have hfw : 2 * d_fw ≤ d_next - 1 :=
    Nat.le_of_lt_succ (WithTop.coe_lt_coe.1 h_fw_dist_lt)
  have hid : (d_next - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_next, BBF_CodeDistance]
    rw [Nat.sub_mul, ← Nat.pow_add, ← Nat.pow_add]
    have h₁ : ℓ + 𝓡 - (i + steps) + steps = ℓ + 𝓡 - i := by omega
    have h₂ : ℓ - (i + steps) + steps = ℓ - i := by omega
    rw [h₁, h₂]
  have hfinite : d_H ≠ ⊤ := by
    dsimp [d_H]
    rw [Code.distFromCode_eq_top_iff_empty f C_i]
    exact Set.nonempty_iff_ne_empty'.mp hC
  let n := ENat.toNat d_H
  have hdH : d_H = n := (ENat.coe_toNat hfinite).symm
  have hn : 2 * n ≤ d_i - 1 := by
    have hn' : n ≤ d_fw * 2 ^ steps := by
      rw [← ENat.coe_le_coe]
      exact le_of_eq_of_le hdH.symm hbridge
    calc
      2 * n ≤ 2 * (d_fw * 2 ^ steps) := by gcongr
      _ = (2 * d_fw) * 2 ^ steps := by rw [mul_assoc]
      _ ≤ (d_next - 1) * 2 ^ steps := by gcongr
      _ = d_i - 1 := hid
  simp only [d_H, n] at hdH
  rw [hdH]
  change ((2 : ℕ) : ℕ∞) * ↑Δ₀(f, C_i).toNat <
    ↑(BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩)
  rw [← ENat.coe_mul, ENat.coe_lt_coe]
  exact Nat.lt_of_le_pred hdpos hn