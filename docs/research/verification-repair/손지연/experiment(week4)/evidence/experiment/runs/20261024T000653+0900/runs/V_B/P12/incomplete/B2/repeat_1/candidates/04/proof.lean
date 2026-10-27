by
  classical
  intro ϑ hϑ_gt_0
  obtain ⟨t, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (n := ϑ) (Nat.ne_of_gt hϑ_gt_0)
  clear hϑ_gt_0
  induction t with
  | zero =>
      intro u hu
      have hbase (r : Fin 1 → F) :
          multilinearCombine (F := F) u r =
            affineLineEvaluation (F := F) (u 0) (u 1) (r 0) := by
        funext j
        simp [multilinearCombine, affineLineEvaluation]
        <;> ring
      have hu' :
          Pr_{let r ← $ᵖ F}[
            Δ₀(affineLineEvaluation (F := F) (u 0) (u 1) r, MC) ≤ e]
            > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
        rw [prob_uniform_eq_card_filter_div_card]
        rw [prob_uniform_eq_card_filter_div_card] at hu
        have hcard :
            (Finset.filter (fun r : Fin 1 → F =>
              Δ₀(multilinearCombine (F := F) u r, MC) ≤ e) Finset.univ).card =
            (Finset.filter (fun r : F =>
              Δ₀(affineLineEvaluation (F := F) (u 0) (u 1) r, MC) ≤ e)
              Finset.univ).card := by
          apply Finset.card_bij (fun r _ => r 0)
          · intro r hr
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            rw [← hbase r]
            exact hr
          · intro r₁ hr₁ r₂ hr₂ h
            funext i
            fin_cases i
            exact h
          · intro r hr
            refine ⟨fun _ => r, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            rw [hbase]
            exact hr
        rw [← hcard]
        have hcardF : Fintype.card (Fin 1 → F) = Fintype.card F := by
          let E : (Fin 1 → F) ≃ F :=
            { toFun := fun r => r 0
              invFun := fun r _ => r
              left_inv := by
                intro r
                funext i
                fin_cases i
                rfl
              right_inv := by intro r; rfl }
          exact Fintype.card_congr E
        simpa [hcardF] using hu
      have h := hC_proximityGapAffineLines (u 0) (u 1) hu'
      unfold jointProximityNat₂ at h
      change jointProximityNat (C := MC) (u := u) e
      convert h using 1
      congr 1
      funext j i
      fin_cases i <;> rfl
  | succ t ih =>
      intro u hu
      let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := Nat.succ t) u).1
      let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := Nat.succ t) u).2
      let E : (Fin (Nat.succ t + 1) → F) ≃ F × (Fin (Nat.succ t) → F) :=
        { toFun := fun r => (r (Fin.last _), fun i => r i.castSucc)
          invFun := fun p => Fin.lastCases p.1 p.2
          left_inv := by
            intro r
            funext i
            refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
          right_inv := by
            intro p
            rcases p with ⟨r, rs⟩
            apply Prod.ext
            · simp
            · funext i
              simp }
      have hu_split :
          Pr_{ let r_last ← $ᵖ F;
               let r_init ← $ᵖ (Fin (Nat.succ t) → F) }[
            multilinearCombine_affineComb_split_last_close
              (MC := MC) (u := u) (e := e) r_last r_init]
            > (((Nat.cast (R := ℝ≥0) (Nat.succ t + 1)) * ε : ℝ≥0) /
                (Fintype.card F : ℝ≥0)) := by
        rw [Pr_multi_let_equiv_single_let]
        rw [do_two_uniform_sampling_eq_uniform_prod]
        rw [prob_uniform_eq_card_filter_div_card]
        rw [prob_uniform_eq_card_filter_div_card] at hu
        have hcard :
            (Finset.filter (fun r : Fin (Nat.succ t + 1) → F =>
              Δ₀(multilinearCombine (F := F) u r, MC) ≤ e) Finset.univ).card =
            (Finset.filter (fun p : F × (Fin (Nat.succ t) → F) =>
              multilinearCombine_affineComb_split_last_close
                (MC := MC) (u := u) (e := e) p.1 p.2) Finset.univ).card := by
          apply Finset.card_bij (fun r _ => E r)
          · intro r hr
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            simpa [E, multilinearCombine_affineComb_split_last_close,
              U₀, U₁, multilinearCombine, affineLineEvaluation] using hr
          · intro r₁ hr₁ r₂ hr₂ h
            exact E.injective h
          · intro p hp
            refine ⟨E.symm p, ?_, E.apply_symm_apply p⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
            simpa [E, multilinearCombine_affineComb_split_last_close,
              U₀, U₁, multilinearCombine, affineLineEvaluation] using hp
        rw [← hcard]
        rw [← Fintype.card_congr E]
        simpa [Nat.succ_eq_add_one] using hu
      have hR_prob :
          Pr_{let r ← $ᵖ F}[
            r ∈ R_star_tensor MC (m := Nat.succ t) (e := e) (ε := ε) U₀ U₁]
            > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
        simpa [U₀, U₁] using
          (prob_R_star_gt_threshold (MC := MC) (ε := ε) (u := u) (e := e)
            hu_split)
      have h_close :
          Pr_{let r ← $ᵖ F}[
            Δ₀(affineLineEvaluation (F := F) (⋈| U₀) (⋈| U₁) r,
              MC ^⋈ (Fin (2 ^ Nat.succ t))) ≤ e]
            > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
        refine lt_of_lt_of_le hR_prob ?_
        apply Pr_le_Pr_of_implies
        intro r hr
        have hr_close := correlatedAgreement_of_mem_R_star_tensor
          (MC := MC) (e := e) (ε := ε) (ϑ_pred := Nat.succ t)
          (ih := ih) (u := u) (r := ⟨r, hr⟩)
        unfold jointProximityNat at hr_close
        convert hr_close using 1
        congr 1
      have hpow : 2 ^ Nat.succ t ≥ 1 :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
      have h_interleaved :=
        h_interleaved_gaps (2 ^ Nat.succ t) hpow
          (⋈| U₀) (⋈| U₁) h_close
      unfold jointProximityNat₂ at h_interleaved
      unfold jointProximityNat at h_interleaved ⊢
      rw [Code.closeToCode_iff_closeToCodeword_of_minDist] at h_interleaved ⊢
      rcases h_interleaved with ⟨v, hv, hdist⟩
      let n := 2 ^ Nat.succ t
      have htotal : 2 ^ (Nat.succ t + 1) = n + n := by
        simp [n, pow_succ, Nat.mul_comm, Nat.mul_two]
      let vflat : InterleavedWord A (Fin (2 ^ (Nat.succ t + 1))) ι :=
        fun j i =>
          if hi : i.val < n then
            v j 0 ⟨i.val, hi⟩
          else
            v j 1 ⟨i.val - n, by
              have hi_lt : i.val < n + n := by
                rw [← htotal]
                exact i.isLt
              omega⟩
      use vflat
      constructor
      · simp only [CodeInterleavable.interleaveCode,
          ModuleCode.moduleInterleavedCode] at hv ⊢
        intro k
        by_cases hk : k.val < n
        · simpa [vflat, hk, Matrix.transpose_apply] using
            (hv 0 ⟨k.val, hk⟩)
        · have hk_le : n ≤ k.val := Nat.le_of_not_gt hk
          have hk_lt : k.val - n < n := by
            have hk_total : k.val < n + n := by
              rw [← htotal]
              exact k.isLt
            omega
          simpa [vflat, hk, Matrix.transpose_apply] using
            (hv 1 ⟨k.val - n, hk_lt⟩)
      · let w := ⋈| finMapTwoWords (⋈| U₀) (⋈| U₁)
        have hcols (j : ι) :
            (⋈| u) j = vflat j ↔ w j = v j := by
          constructor
          · intro hj
            funext b k
            fin_cases b
            · have hk := congrFun hj
                ⟨k.val, by
                  rw [htotal]
                  omega⟩
              simpa [w, vflat, n, U₀, U₁,
                splitHalfRowWiseInterleavedWords,
                Interleavable.interleave, finMapTwoWords] using hk
            · let idx : Fin (2 ^ (Nat.succ t + 1)) :=
                ⟨k.val + n, by
                  rw [htotal]
                  omega⟩
              have hk := congrFun hj idx
              have hidx : ¬idx.val < n := by
                dsimp only [idx]
                omega
              simpa [w, idx, vflat, hidx, n, U₀, U₁,
                splitHalfRowWiseInterleavedWords,
                Interleavable.interleave, finMapTwoWords] using hk
          · intro hj
            funext i
            by_cases hi : i.val < n
            · have hk := congrFun (congrFun hj 0) ⟨i.val, hi⟩
              simpa [w, vflat, hi, n, U₀, U₁,
                splitHalfRowWiseInterleavedWords,
                Interleavable.interleave, finMapTwoWords] using hk
            · have hi_le : n ≤ i.val := Nat.le_of_not_gt hi
              have hi_lt : i.val - n < n := by
                have hi_total : i.val < n + n := by
                  rw [← htotal]
                  exact i.isLt
                omega
              have hk := congrFun (congrFun hj 1) ⟨i.val - n, hi_lt⟩
              simpa [w, vflat, hi, hi_le, n, U₀, U₁,
                splitHalfRowWiseInterleavedWords,
                Interleavable.interleave, finMapTwoWords,
                Nat.sub_add_cancel] using hk
        have hdist_eq :
            Δ₀((⋈| u), vflat) = Δ₀(w, v) := by
          unfold hammingDist
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact not_congr (hcols j)
        rw [hdist_eq]
        exact hdist