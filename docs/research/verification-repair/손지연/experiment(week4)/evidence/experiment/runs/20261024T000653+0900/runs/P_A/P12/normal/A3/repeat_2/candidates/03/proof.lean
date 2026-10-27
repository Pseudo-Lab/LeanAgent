by
  classical
  intro ϑ
  induction ϑ with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp only [zero_add, gt_iff_lt, zero_lt_one, ModuleCode, forall_const]
      intro u hprob
      let h_affine := multilinearCombine₁_eq_affineLineEvaluation (F := F) (u := u)
      simp_rw [h_affine] at hprob
      let h_uniform := prob_uniform_singleton_finFun_eq (F := F)
        (P := fun r => Δ₀(affineLineEvaluation (u 0) (u 1) r, MC) ≤ e)
      simp_rw [h_uniform, Nat.cast_one, ENNReal.coe_one, one_mul] at hprob
      have hCA := hC_proximityGapAffineLines (u 0) (u 1) hprob
      simp only [jointProximityNat₂, Fin.isValue] at hCA
      have hu : u = finMapTwoWords (u 0) (u 1) := by
        funext i
        match i with
        | 0 => rfl
        | 1 => rfl
      rw [hu.symm] at hCA
      exact hCA
    | succ k =>
      intro _ u hprob
      let p := k + 1
      set U₀ : Fin (2 ^ p) → Word A ι :=
        (splitHalfRowWiseInterleavedWords (ϑ := p) u).1
      set U₁ : Fin (2 ^ p) → Word A ι :=
        (splitHalfRowWiseInterleavedWords (ϑ := p) u).2
      unfold jointProximityNat
      simp only
      have hsnoc : ∀ r : Fin (p + 1) → F,
          Fin.snoc (fun i : Fin p => r i.castSucc) (r (Fin.last p)) = r := by
        intro r
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      let P : F → (Fin p → F) → Prop := fun r_last r_init =>
        Δ₀(multilinearCombine (u := u) (r := Fin.snoc r_init r_last), MC) ≤ e
      let hsplit := prob_split_last_uniform_sampling_of_finFun
        (ϑ := p) (F := F) (P := P)
      unfold P at hsplit
      simp_rw [hsnoc] at hsplit
      rw [hsplit] at hprob
      have hrecursive (r_init : Fin p → F) (r_last : F) :
          multilinearCombine u (Fin.snoc r_init r_last) =
            multilinearCombine (affineLineEvaluation U₀ U₁ r_last) r_init := by
        rw [multilinearCombine_recursive_form]
        simp only [Fin.snoc_last, Fin.init_snoc]
        rfl
      simp_rw [hrecursive] at hprob
      let Rset := R_star_tensor MC (m := p) (e := e) (ε := ε) U₀ U₁
      have hp : Pr_{let r ← $ᵖ F}[r ∈ Rset] >
          (↑ε : ENNReal) / (Fintype.card F : ENNReal) :=
        prob_R_star_gt_threshold (MC := MC) (ε := ε) (ϑ := p)
          (u := u) (e := e) hprob
      have ihp : δ_ε_multilinearCorrelatedAgreement_Nat
          (F := F) (A := A) (ι := ι) (C := MC) (ϑ := p) (e := e) (ε := ε) :=
        ih (Nat.succ_pos k)
      have hline : ∀ r : Rset,
          jointProximityNat (u := affineLineEvaluation U₀ U₁ r.val)
            (e := e) (C := MC) := by
        intro r
        exact correlatedAgreement_of_mem_R_star_tensor (ih := ihp) (u := u) r
      let W₀ : InterleavedWord A (Fin (2 ^ p)) ι := fun j i => U₀ i j
      let W₁ : InterleavedWord A (Fin (2 ^ p)) ι := fun j i => U₁ i j
      have hline_prob : Pr_{let r ← $ᵖ F}[
          Δ₀(affineLineEvaluation W₀ W₁ r, MC ^⋈ (Fin (2 ^ p))) ≤ e] >
          (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
        apply lt_of_le_of_lt' _ hp
        apply Pr_le_Pr_of_implies
        intro r hr
        have h := hline ⟨r, hr⟩
        unfold jointProximityNat at h
        change Δ₀(⋈|affineLineEvaluation U₀ U₁ r,
          interleavedCodeSet (MC : Set (Word A ι))) ≤ e
        exact h
      have hfinal :=
        h_interleaved_gaps (2 ^ p) Nat.one_le_two_pow W₀ W₁ hline_prob
      apply CA_split_rowwise_implies_CA (u := u) (e := e)
      change jointProximityNat₂ (C := MC ^⋈ (Fin (2 ^ p))) W₀ W₁ e
      exact hfinal