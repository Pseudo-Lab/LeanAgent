by
  classical
  intro ϑ hϑ_gt_0
  induction ϑ, hϑ_gt_0 using Nat.le_induction with
  | base =>
      intro u h_close
      have hu : finMapTwoWords (u 0) (u 1) = u := by
        funext i j
        fin_cases i <;> rfl
      have h_affine := hC_proximityGapAffineLines (u 0) (u 1)
      apply hu ▸ h_affine
      convert h_close using 1 <;>
        simp [multilinearCombine, affineLineEvaluation,
          PMF.uniformOfFintype_apply, Fin.sum_univ_two]
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
        convert h_close using 1 <;>
          simp [multilinearCombine_affineComb_split_last_close,
            multilinearCombine, splitHalfRowWiseInterleavedWords,
            affineLineEvaluation, PMF.uniformOfFintype_apply,
            Fin.sum_univ_succ, pow_succ] <;>
          ext <;> simp [Fin.lastCases, pow_succ] <;> omega
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
        have h_joint := correlatedAgreement_of_mem_R_star_tensor
          (MC := MC) (e := e) (ε := ε) (ϑ_pred := ϑ) ih u
          (⟨r, hr⟩ : R_star_tensor MC (m := ϑ) (e := e) (ε := ε) U₀ U₁)
        convert h_joint using 1 <;>
          simp [jointProximityNat, U₀, U₁, Interleavable.interleave,
            affineLineEvaluation, Matrix.transpose_apply, Pi.add_apply,
            Pi.smul_apply] <;>
          ext <;> simp [Matrix.transpose_apply]
      have hpow : 2 ^ ϑ ≥ 1 := by
        exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero ϑ (by decide))
      have h_joint_halves :=
        (h_interleaved_gaps (2 ^ ϑ) hpow)
          (⋈| U₀) (⋈| U₁) h_affine_probability
      convert h_joint_halves using 1 <;>
        simp [jointProximityNat₂, jointProximityNat, U₀, U₁,
          splitHalfRowWiseInterleavedWords, finMapTwoWords,
          Interleavable.interleave, CodeInterleavable.interleaveCode,
          interleavedCodeSet, Matrix.transpose_apply, pow_succ] <;>
        ext <;> simp [Matrix.transpose_apply, pow_succ] <;> omega