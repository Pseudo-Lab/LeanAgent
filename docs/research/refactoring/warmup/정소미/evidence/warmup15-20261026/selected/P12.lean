theorem interleaved_affine_gaps_imply_tensor_gaps
    (hC_proximityGapAffineLines : e_ε_correlatedAgreementAffineLinesNat
      (F := F) (A := A) (ι := ι) (C := MC) (e := e) (ε := ε))
    (h_interleaved_gaps : ∀ m : ℕ, m ≥ 1 →
      e_ε_correlatedAgreementAffineLinesNat (F := F)
        (A := InterleavedSymbol A (Fin m)) (ι := ι) (C := MC ^⋈ (Fin m)) e ε) :
    ∀ (ϑ : ℕ), (hϑ_gt_0 : ϑ > 0) → δ_ε_multilinearCorrelatedAgreement_Nat (F := F) (A := A)
      (ι := ι) (C := MC) (ϑ := ϑ) (e := e) (ε := ε) := by
  classical
  intro ϑ
  induction ϑ with
  | zero =>
      intro h
      omega
  | succ n ih =>
      cases n with
      | zero =>
          simp only [zero_add, gt_iff_lt, zero_lt_one, ModuleCode, forall_const]
          intro u hprob
          let h_aff := multilinearCombine₁_eq_affineLineEvaluation (F := F) (u := u)
          simp_rw [h_aff] at hprob
          let h_single := prob_uniform_singleton_finFun_eq (F := F)
            (P := fun r => Δ₀(affineLineEvaluation (u 0) (u 1) r, MC) ≤ e)
          simp_rw [h_single, Nat.cast_one, ENNReal.coe_one, one_mul] at hprob
          have h := hC_proximityGapAffineLines (u 0) (u 1) hprob
          simp only [jointProximityNat₂, Fin.isValue] at h
          have hu : u = finMapTwoWords (u 0) (u 1) := by
            funext i
            match i with
            | 0 => rfl
            | 1 => rfl
          rw [hu.symm] at h
          exact h
      | succ k =>
          intro _ u hprob
          set U₀ : Fin (2 ^ (k + 1)) → Word A ι :=
            (splitHalfRowWiseInterleavedWords (ϑ := k + 1) u).1
          set U₁ : Fin (2 ^ (k + 1)) → Word A ι :=
            (splitHalfRowWiseInterleavedWords (ϑ := k + 1) u).2
          unfold jointProximityNat
          simp only
          let P : F → (Fin (k + 1) → F) → Prop := fun r_last r_init =>
            Δ₀(multilinearCombine (u := u) (r := Fin.snoc r_init r_last), MC) ≤ e
          let h_split := prob_split_last_uniform_sampling_of_finFun
            (ϑ := k + 1) (F := F) (P := P)
          unfold P at h_split
          simp_rw [← Fin.init_def, Fin.snoc_init_self] at h_split
          rw [h_split] at hprob
          have h_rec (r_init : Fin (k + 1) → F) (r_last : F) :
              multilinearCombine u (Fin.snoc r_init r_last) =
                multilinearCombine (affineLineEvaluation U₀ U₁ r_last) r_init := by
            rw [multilinearCombine_recursive_form]
            simp only [Fin.snoc_last, Fin.init_snoc]
            rfl
          simp_rw [h_rec] at hprob
          let R := R_star_tensor MC (m := k + 1) (e := e) (ε := ε) U₀ U₁
          have hR : Pr_{let r ← $ᵖ F}[r ∈ R] >
              (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            exact prob_R_star_gt_threshold (MC := MC) (ε := ε) (ϑ := k + 1)
              (u := u) (e := e) hprob
          have hclose : ∀ r : R,
              jointProximityNat (u := affineLineEvaluation U₀ U₁ r.val)
                (e := e) (C := MC) := by
            intro r
            apply correlatedAgreement_of_mem_R_star_tensor
              (ih := fun u' => ih (by omega) u') (u := u)
          have hline :
              Pr_{let r ← $ᵖ F}[
                Δ₀(affineLineEvaluation
                    (u₀ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₀))
                    (u₁ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₁)) r,
                  MC ^⋈ (Fin (2 ^ (k + 1)))) ≤ e] >
                (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            apply lt_of_le_of_lt' _ hR
            apply Pr_le_Pr_of_implies
            intro r hr
            have h := hclose ⟨r, hr⟩
            unfold jointProximityNat at h
            exact h
          have hfinal : jointProximityNat₂
              (u₀ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₀))
              (u₁ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₁))
              (e := e) (C := MC ^⋈ (Fin (2 ^ (k + 1)))) := by
            apply h_interleaved_gaps (2 ^ (k + 1)) Nat.one_le_two_pow
            exact hline
          exact CA_split_rowwise_implies_CA (MC : Set (Word A ι))
            (u := u) (e := e) hfinal