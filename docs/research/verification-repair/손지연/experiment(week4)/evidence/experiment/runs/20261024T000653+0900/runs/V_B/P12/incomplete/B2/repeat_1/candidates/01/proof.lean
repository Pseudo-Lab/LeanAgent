by
  classical
  intro ϑ hϑ_gt_0
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega)
  induction t with
  | zero =>
      simpa [δ_ε_multilinearCorrelatedAgreement_Nat, multilinearCombine,
        jointProximityNat₂, jointProximityNat, finMapTwoWords] using
        hC_proximityGapAffineLines
  | succ t ih =>
      intro u hu
      let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := Nat.succ t) u).1
      let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := Nat.succ t) u).2
      have hu_split :
          Pr_{ let r_last ← $ᵖ F;
               let r_init ← $ᵖ (Fin (Nat.succ t) → F) }[
            multilinearCombine_affineComb_split_last_close
              (MC := MC) (u := u) (e := e) r_last r_init]
            > (((Nat.cast (R := ℝ≥0) (Nat.succ t + 1)) * ε : ℝ≥0) /
                (Fintype.card F : ℝ≥0)) := by
        simpa [multilinearCombine_affineComb_split_last_close, U₀, U₁,
          Nat.succ_eq_add_one] using hu
      have hR_prob :
          Pr_{ let r ← $ᵖ F }[
            r ∈ R_star_tensor MC (m := Nat.succ t) (e := e) (ε := ε) U₀ U₁]
            > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
        simpa [U₀, U₁] using
          (prob_R_star_gt_threshold (MC := MC) (ε := ε) (u := u) (e := e)
            hu_split)
      have h_close :
          Pr_{ let r ← $ᵖ F }[
            Δ₀(affineLineEvaluation (F := F) (⋈| U₀) (⋈| U₁) r,
              MC ^⋈ (Fin (2 ^ Nat.succ t))) ≤ e]
            > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
        refine lt_of_lt_of_le hR_prob ?_
        apply Pr_le_Pr_of_implies
        intro r hr
        have hr_close := correlatedAgreement_of_mem_R_star_tensor
          (MC := MC) (e := e) (ε := ε) (ϑ_pred := Nat.succ t)
          (ih := ih) (u := u)
          (r := ⟨r, hr⟩)
        simpa [jointProximityNat, affineLineEvaluation,
          Interleavable.interleave, U₀, U₁] using hr_close
      have h_interleaved :=
        h_interleaved_gaps (2 ^ Nat.succ t) (by positivity)
          (⋈| U₀) (⋈| U₁) h_close
      simpa [jointProximityNat₂, jointProximityNat,
        splitHalfRowWiseInterleavedWords, U₀, U₁] using h_interleaved