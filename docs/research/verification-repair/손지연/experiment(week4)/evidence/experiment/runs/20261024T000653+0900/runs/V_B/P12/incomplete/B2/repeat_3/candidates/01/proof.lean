by
  classical
  intro ϑ hϑ_gt_0
  induction ϑ, hϑ_gt_0 using Nat.le_induction with
  | base =>
      simpa using hC_proximityGapAffineLines
  | succ ϑ hϑ_ge_one ih =>
      intro u h_close
      let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
      let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
      have h_split_close :
          Pr_{ let r_last ← $ᵖ F;
               let r_init ← $ᵖ (Fin ϑ → F) }[
            multilinearCombine_affineComb_split_last_close
              (MC := MC) (u := u) (e := e) r_last r_init ]
            > (((Nat.cast (R := ℝ≥0) (ϑ + 1)) * ε : ℝ≥0) /
                (Fintype.card F : ℝ≥0)) := by
        simpa [multilinearCombine_affineComb_split_last_close] using h_close
      have hR :
          Pr_{ let r ← $ᵖ F }[
            r ∈ R_star_tensor MC (m := ϑ) (e := e) (ε := ε) U₀ U₁ ]
            > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
        simpa [U₀, U₁] using
          (prob_R_star_gt_threshold (MC := MC) (ε := ε)
            (ϑ := ϑ) u e h_split_close)
      have h_affine_probability :
          Pr_{ let r ← $ᵖ F }[
            Δ₀(affineLineEvaluation (F := F) (⋈| U₀) (⋈| U₁) r,
              MC ^⋈ (Fin (2 ^ ϑ))) ≤ e ]
            > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
        apply lt_of_lt_of_le hR
        apply Pr_le_Pr_of_implies
        intro r hr
        have hr' : r ∈ R_star_tensor MC (m := ϑ) (e := e) (ε := ε) U₀ U₁ := hr
        have h_joint := correlatedAgreement_of_mem_R_star_tensor
          (MC := MC) (e := e) (ε := ε) (ϑ_pred := ϑ) ih u
          (⟨r, hr'⟩ : R_star_tensor MC (m := ϑ) (e := e) (ε := ε) U₀ U₁)
        simpa [jointProximityNat, U₀, U₁] using h_joint
      have h_joint_halves :=
        (h_interleaved_gaps (2 ^ ϑ) (by positivity))
          (⋈| U₀) (⋈| U₁) h_affine_probability
      simpa [jointProximityNat₂, jointProximityNat, U₀, U₁,
        splitHalfRowWiseInterleavedWords] using h_joint_halves