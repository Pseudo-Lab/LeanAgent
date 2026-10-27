by
  classical
  intro ϑ
  induction ϑ using Nat.strong_induction_on with
  | h ϑ ih =>
      intro hϑ_gt_0
      cases ϑ with
      | zero => omega
      | succ ϑ_pred =>
          by_cases hϑ_pred : ϑ_pred = 0
          · subst ϑ_pred
            unfold δ_ε_multilinearCorrelatedAgreement_Nat
            intro u hu
            let u₀ : Word A ι := u 0
            let u₁ : Word A ι := u 1
            have hfin : finMapTwoWords u₀ u₁ = u := by
              funext i
              fin_cases i <;> rfl
            rw [← hfin]
            apply hC_proximityGapAffineLines
            rw [prob_uniform_eq_card_filter_div_card] at hu ⊢
            have hcard :
                (Finset.filter
                    (fun r : Fin 1 → F =>
                      Δ₀(multilinearCombine u r, MC) ≤ e)
                    Finset.univ).card =
                  (Finset.filter
                    (fun r : F =>
                      Δ₀(affineLineEvaluation u₀ u₁ r, MC) ≤ e)
                    Finset.univ).card := by
              apply Finset.card_bij (fun r _ => r 0)
              · intro r hr
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
                simpa [multilinearCombine, affineLineEvaluation, u₀, u₁] using hr
              · intro r₁ hr₁ r₂ hr₂ h
                funext i
                fin_cases i
                exact h
              · intro r hr
                refine ⟨fun _ => r, ?_, rfl⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
                simpa [multilinearCombine, affineLineEvaluation, u₀, u₁] using hr
            simpa [hcard, Fintype.card_fun] using hu
          · have hϑ_pred_gt_0 : ϑ_pred > 0 := Nat.pos_of_ne_zero hϑ_pred
            have ih_pred : δ_ε_multilinearCorrelatedAgreement_Nat
                (F := F) (A := A) (ι := ι) (C := MC) (ϑ := ϑ_pred)
                (e := e) (ε := ε) :=
              ih ϑ_pred (Nat.lt_succ_self ϑ_pred) hϑ_pred_gt_0
            unfold δ_ε_multilinearCorrelatedAgreement_Nat
            intro u hP
            let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ_pred) u).1
            let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ_pred) u).2
            let R := R_star_tensor MC (m := ϑ_pred) (e := e) (ε := ε) U₀ U₁
            have hP' :
                Pr_{ let r_last ← $ᵖ F;
                     let r_init ← $ᵖ (Fin ϑ_pred → F) }[
                  multilinearCombine_affineComb_split_last_close
                    (MC := MC) (u := u) (e := e) r_last r_init] >
                  ((ϑ_pred + 1 : ℝ≥0) * ε) /
                    (Fintype.card F : ℝ≥0) := by
              simpa [multilinearCombine_affineComb_split_last_close,
                multilinearCombine, U₀, U₁] using hP
            have hR :
                Pr_{let r ← $ᵖ F}[r ∈ R] >
                  (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
              simpa only [U₀, U₁, R] using
                prob_R_star_gt_threshold (MC := MC) (ε := ε)
                  (u := u) (e := e) hP'
            have h_affine :
                Pr_{let r ← $ᵖ F}[
                    Δ₀(affineLineEvaluation (F := F) (⋈| U₀) (⋈| U₁) r,
                      MC ^⋈ (Fin (2 ^ ϑ_pred))) ≤ e] >
                  (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
              apply lt_of_lt_of_le hR
              apply Pr_le_Pr_of_implies
              intro r hr
              have hr_mem : r ∈ R_star_tensor MC (e := e) (ε := ε) U₀ U₁ := by
                change r ∈ R
                exact hr
              have hr' := correlatedAgreement_of_mem_R_star_tensor
                (MC := MC) (e := e) (ε := ε) (ih := ih_pred) (u := u)
                (r := ⟨r, by
                  change r ∈ R_star_tensor MC (e := e) (ε := ε) U₀ U₁
                  exact hr_mem⟩)
              rw [jointProximityNat] at hr'
              change Δ₀(affineLineEvaluation (F := F) (⋈| U₀) (⋈| U₁) r,
                MC ^⋈ (Fin (2 ^ ϑ_pred))) ≤ e
              exact hr'
            have hpow : 1 ≤ 2 ^ ϑ_pred := Nat.one_le_pow ϑ_pred 2 (by omega)
            have h_pair := h_interleaved_gaps (2 ^ ϑ_pred) hpow
              (⋈| U₀) (⋈| U₁) h_affine
            simpa [jointProximityNat₂, U₀, U₁, splitHalfRowWiseInterleavedWords,
              finMapTwoWords, Nat.pow_succ] using h_pair