by
  classical
  have prob_snoc (n : ℕ) (P : (Fin (n + 1) → F) → Prop) :
      Pr_{ let r_last ← $ᵖ F;
           let r_init ← $ᵖ (Fin n → F) }[
        P (Fin.snoc r_init r_last)] =
      Pr_{ let r ← $ᵖ (Fin (n + 1) → F) }[P r] := by
    rw [Pr_multi_let_equiv_single_let]
    rw [do_two_uniform_sampling_eq_uniform_prod]
    rw [prob_uniform_eq_card_filter_div_card]
    rw [prob_uniform_eq_card_filter_div_card]
    congr 1
    · refine Finset.card_bij
        (fun p _ => Fin.snoc p.2 p.1) ?_ ?_ ?_
      · intro p hp
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp
      · intro p₁ hp₁ p₂ hp₂ h
        apply Prod.ext
        · have hlast := congrFun h (Fin.last n)
          simpa using hlast
        · funext i
          have hinit := congrFun h i.castSucc
          simpa using hinit
      · intro r hr
        refine ⟨(r (Fin.last n), fun i => r i.castSucc), ?_, ?_⟩
        · simpa only [Finset.mem_filter, Finset.mem_univ, true_and]
          using hr
        · funext i
          refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    · simp [Fintype.card_fun, pow_succ']
  have multilinearCombine_snoc
      (n : ℕ) (u : WordStack A (Fin (2 ^ (n + 1))) ι)
      (r_init : Fin n → F) (r_last : F) :
      multilinearCombine u (Fin.snoc r_init r_last) =
        multilinearCombine
          (affineLineEvaluation
            (splitHalfRowWiseInterleavedWords (ϑ := n) u).1
            (splitHalfRowWiseInterleavedWords (ϑ := n) u).2 r_last)
          r_init := by
    rfl
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
          have hprob_eq := prob_snoc 0
            (fun r : Fin 1 → F => Δ₀(multilinearCombine u r, MC) ≤ e)
          rw [← hprob_eq] at hu
          simpa [multilinearCombine_snoc, affineLineEvaluation,
            splitHalfRowWiseInterleavedWords] using hu
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
          have hprob_eq := prob_snoc ϑ
            (fun r : Fin (ϑ + 1) → F => Δ₀(multilinearCombine u r, MC) ≤ e)
          rw [← hprob_eq] at hu
          simpa only [multilinearCombine_affineComb_split_last_close,
            multilinearCombine_snoc] using hu
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
          rw [jointProximityNat] at hr_close
          have hinterleave :
              affineLineEvaluation (F := F) (⋈| U₀) (⋈| U₁) r =
                ⋈| (affineLineEvaluation (F := F) U₀ U₁ r) := by
            ext j k
            rfl
          rw [hinterleave]
          simpa only [U₀, U₁] using hr_close
        have hpow : 2 ^ ϑ ≥ 1 := Nat.one_le_pow ϑ 2 (by omega)
        have hpair :=
          (h_interleaved_gaps (2 ^ ϑ) hpow)
            (⋈| U₀) (⋈| U₁) hline
        unfold jointProximityNat₂ at hpair
        rw [jointProximityNat] at hpair ⊢
        simpa [U₀, U₁, splitHalfRowWiseInterleavedWords,
          Interleavable.interleave, CodeInterleavable.interleaveCode,
          ModuleCode.moduleInterleavedCode, Matrix.transpose_transpose,
          Matrix.transpose_apply, Nat.succ_eq_add_one] using hpair