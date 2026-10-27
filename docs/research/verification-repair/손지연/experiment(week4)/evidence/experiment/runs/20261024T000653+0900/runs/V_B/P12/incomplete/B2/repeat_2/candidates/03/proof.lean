by
  classical
  intro ϑ
  induction ϑ with
  | zero =>
      intro hϑ
      omega
  | succ ϑ ih =>
      intro _
      by_cases hϑ_zero : ϑ = 0
      · subst ϑ
        intro u hu
        have hprob :
            Pr_{ let r ← $ᵖ F }[
              Δ₀(affineLineEvaluation (F := F) (u 0) (u 1) r, MC) ≤ e]
              > (ε : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
          convert hu using 1 <;>
            simp [multilinearCombine, affineLineEvaluation,
              Pr_multi_let_equiv_single_let,
              do_two_uniform_sampling_eq_uniform_prod]
        have hbase := hC_proximityGapAffineLines (u 0) (u 1) hprob
        have hu_pair : finMapTwoWords (u 0) (u 1) = u := by
          funext i
          fin_cases i <;> rfl
        simpa [jointProximityNat₂, hu_pair] using hbase
      · have hϑ_pos : ϑ > 0 := by
          omega
        have ihϑ : δ_ε_multilinearCorrelatedAgreement_Nat
            (F := F) (A := A) (ι := ι) (C := MC)
            (ϑ := ϑ) (e := e) (ε := ε) := ih hϑ_pos
        intro u hu
        let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
        let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
        let R := R_star_tensor MC (m := ϑ) (e := e) (ε := ε) U₀ U₁
        have hu_split :
            Pr_{ let r_last ← $ᵖ F;
                 let r_init ← $ᵖ (Fin ϑ → F) }[
              multilinearCombine_affineComb_split_last_close
                (MC := MC) (u := u) (e := e) r_last r_init]
              > (((Nat.cast (R := ℝ≥0) (ϑ + 1)) * ε : ℝ≥0) /
                  (Fintype.card F : ℝ≥0)) := by
          convert hu using 1 <;>
            simp [multilinearCombine_affineComb_split_last_close,
              splitHalfRowWiseInterleavedWords, multilinearCombine,
              Pr_multi_let_equiv_single_let,
              do_two_uniform_sampling_eq_uniform_prod,
              Nat.succ_eq_add_one]
        have hR_raw :=
          prob_R_star_gt_threshold (MC := MC) (ε := ε)
            (ϑ := ϑ) u e hu_split
        have hR :
            Pr_{ let r ← $ᵖ F }[r ∈ R]
              > (ε : ENNReal) / (Fintype.card F : ENNReal) := by
          simpa only [U₀, U₁, R] using hR_raw
        have hline :
            Pr_{ let r ← $ᵖ F }[
              Δ₀(affineLineEvaluation (F := F) (⋈| U₀) (⋈| U₁) r,
                MC ^⋈ (Fin (2 ^ ϑ))) ≤ e]
              > (ε : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
          refine lt_of_lt_of_le hR ?_
          apply Pr_le_Pr_of_implies
          intro r hr
          have hr_mem :
              r ∈ R_star_tensor MC (m := ϑ) (e := e) (ε := ε)
                (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
                (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2 := by
            change r ∈ R
            exact hr
          have hr_close := correlatedAgreement_of_mem_R_star_tensor
            (MC := MC) (e := e) (ε := ε) (ϑ_pred := ϑ) ihϑ u
            ⟨r, hr_mem⟩
          convert hr_close using 1 <;>
            simp [jointProximityNat, U₀, U₁,
              splitHalfRowWiseInterleavedWords, affineLineEvaluation,
              Interleavable.interleave, interleave_wordStack_eq]
        have hpow : 2 ^ ϑ ≥ 1 := Nat.one_le_pow ϑ 2 (by omega)
        have hpair :=
          (h_interleaved_gaps (2 ^ ϑ) hpow)
            (⋈| U₀) (⋈| U₁) hline
        convert hpair using 1 <;>
          simp [U₀, U₁, jointProximityNat₂, jointProximityNat,
            splitHalfRowWiseInterleavedWords, finMapTwoWords,
            Interleavable.interleave, interleave_wordStack_eq,
            CodeInterleavable.interleaveCode,
            ModuleCode.moduleInterleavedCode, Nat.succ_eq_add_one]