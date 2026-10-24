by
  classical
  have prob_uniform_equiv
      {α β : Type} [Fintype α] [Fintype β]
      (E : α ≃ β) (p : β → Prop) :
      Pr_{let x ← $ᵖ α}[p (E x)] = Pr_{let y ← $ᵖ β}[p y] := by
    have hcard :
        (Finset.filter (fun x : α => p (E x)) Finset.univ).card =
          (Finset.filter p Finset.univ).card := by
      refine Finset.card_bij (fun x _ => E x) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx
      · intro x₁ hx₁ x₂ hx₂ h
        exact E.injective h
      · intro y hy
        refine ⟨E.symm y, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
          simpa using hy
        · simp
    rw [prob_uniform_eq_card_filter_div_card,
      prob_uniform_eq_card_filter_div_card]
    rw [hcard, Fintype.card_congr E]
  intro ϑ hϑ_gt_0
  induction ϑ using Nat.case_strong_induction_on with
  | hz => omega
  | hi ϑ ih =>
      by_cases hϑ_zero : ϑ = 0
      · subst ϑ
        intro u hu
        let E : F ≃ (Fin 1 → F) where
          toFun := fun r _ => r
          invFun := fun r => r 0
          left_inv := fun r => rfl
          right_inv := by
            intro r
            funext i
            fin_cases i
            rfl
        have hp :
            Pr_{let r ← $ᵖ F}[
              Δ₀(multilinearCombine (F := F) u (E r), MC) ≤ e]
              > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
          rw [prob_uniform_equiv E
            (fun r => Δ₀(multilinearCombine (F := F) u r, MC) ≤ e)]
          simpa [δ_ε_multilinearCorrelatedAgreement_Nat] using hu
        have hbase := hC_proximityGapAffineLines (u 0) (u 1) (by
          simpa [E, multilinearCombine, affineLineEvaluation] using hp)
        simpa [jointProximityNat₂, finMapTwoWords] using hbase
      · have hϑ_pos : 0 < ϑ := Nat.pos_of_ne_zero hϑ_zero
        have ihϑ : δ_ε_multilinearCorrelatedAgreement_Nat
            (F := F) (A := A) (ι := ι) (C := MC) (ϑ := ϑ) (e := e) (ε := ε) :=
          ih ϑ (Nat.le_refl ϑ) hϑ_pos
        intro u hu
        let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
        let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
        let R := R_star_tensor MC (m := ϑ) (e := e) (ε := ε) U₀ U₁
        let E : (F × (Fin ϑ → F)) ≃ (Fin (ϑ + 1) → F) where
          toFun := fun p => Fin.lastCases p.1 p.2
          invFun := fun r => (r (Fin.last ϑ), fun i => r i.castSucc)
          left_inv := by
            intro p
            rcases p with ⟨r, rs⟩
            apply Prod.ext
            · rfl
            · funext i
              rfl
          right_inv := by
            intro r
            funext i
            refine Fin.lastCases ?_ (fun j => ?_) i <;> rfl
        have hu_split :
            Pr_{ let r_last ← $ᵖ F;
                 let r_init ← $ᵖ (Fin ϑ → F)}[
              multilinearCombine_affineComb_split_last_close
                (MC := MC) (u := u) (e := e) r_last r_init]
              > (((Nat.cast (R := ℝ≥0) (ϑ + 1)) * ε : ℝ≥0) /
                (Fintype.card F : ℝ≥0)) := by
          rw [do_two_uniform_sampling_eq_uniform_prod]
          have hp :
              Pr_{let p ← $ᵖ (F × (Fin ϑ → F))}[
                Δ₀(multilinearCombine (F := F) u (E p), MC) ≤ e]
                > (((Nat.cast (R := ℝ≥0) (ϑ + 1)) * ε : ℝ≥0) /
                  (Fintype.card F : ℝ≥0)) := by
            rw [prob_uniform_equiv E
              (fun r => Δ₀(multilinearCombine (F := F) u r, MC) ≤ e)]
            simpa [δ_ε_multilinearCorrelatedAgreement_Nat] using hu
          simpa [multilinearCombine_affineComb_split_last_close, E, U₀, U₁,
            multilinearCombine, splitHalfRowWiseInterleavedWords,
            affineLineEvaluation] using hp
        have hR :
            Pr_{let r ← $ᵖ F}[r ∈ R] >
              (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
          simpa [U₀, U₁, R] using
            (prob_R_star_gt_threshold (MC := MC) (ε := ε)
              (u := u) (e := e) hu_split)
        have hclose : ∀ r : R,
            jointProximityNat
              (u := affineLineEvaluation U₀ U₁ r.val)
              (e := e) (C := MC) := by
          simpa [U₀, U₁, R] using
            (correlatedAgreement_of_mem_R_star_tensor
              (MC := MC) (e := e) (ε := ε) (ih := ihϑ) u)
        have h_affine_probability :
            Pr_{let r ← $ᵖ F}[
              Δ₀(affineLineEvaluation (F := F) (⋈| U₀) (⋈| U₁) r,
                MC ^⋈ (Fin (2 ^ ϑ))) ≤ e]
              > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
          apply lt_of_lt_of_le hR
          apply Pr_le_Pr_of_implies
          intro r hr
          have hword :
              affineLineEvaluation (F := F) (⋈| U₀) (⋈| U₁) r =
                ⋈| (affineLineEvaluation (F := F) U₀ U₁ r) := by
            ext j k
            rfl
          rw [hword]
          simpa [jointProximityNat] using hclose ⟨r, hr⟩
        have hpow : 0 < 2 ^ ϑ := pow_pos (by omega) ϑ
        have h_interleaved :=
          (h_interleaved_gaps (2 ^ ϑ) (by omega))
            (⋈| U₀) (⋈| U₁) h_affine_probability
        unfold jointProximityNat₂ at h_interleaved
        unfold jointProximityNat at h_interleaved ⊢
        rw [Code.closeToCode_iff_closeToCodeword_of_minDist] at h_interleaved ⊢
        rcases h_interleaved with ⟨v, hv, hv_close⟩
        let flatV : InterleavedWord A (Fin (2 ^ (ϑ + 1))) ι := fun j i =>
          if hi : i.val < 2 ^ ϑ then
            v j 0 ⟨i.val, hi⟩
          else
            v j 1 ⟨i.val - 2 ^ ϑ, by
              have hil := i.isLt
              rw [pow_succ] at hil
              omega⟩
        refine ⟨flatV, ?_, ?_⟩
        · simp only [CodeInterleavable.interleaveCode,
            ModuleCode.moduleInterleavedCode] at hv ⊢
          intro i
          by_cases hi : i.val < 2 ^ ϑ
          · simpa [flatV, hi] using hv 0 ⟨i.val, hi⟩
          · have hil := i.isLt
            have hisub : i.val - 2 ^ ϑ < 2 ^ ϑ := by
              rw [pow_succ] at hil
              omega
            simpa [flatV, hi] using hv 1 ⟨i.val - 2 ^ ϑ, hisub⟩
        · have hdist :
              Δ₀(⋈| u, flatV) =
                Δ₀(⋈| finMapTwoWords (⋈| U₀) (⋈| U₁), v) := by
            unfold hammingDist
            apply congrArg Finset.card
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            apply not_congr
            constructor
            · intro hflat
              funext k t
              fin_cases k
              · let i : Fin (2 ^ (ϑ + 1)) := ⟨t.val, by
                  rw [pow_succ]
                  omega⟩
                have hi : i.val < 2 ^ ϑ := t.isLt
                have h := congrFun hflat i
                simpa [i, flatV, hi, U₀, U₁, finMapTwoWords,
                  splitHalfRowWiseInterleavedWords] using h
              · let i : Fin (2 ^ (ϑ + 1)) := ⟨2 ^ ϑ + t.val, by
                  rw [pow_succ]
                  omega⟩
                have hi : ¬i.val < 2 ^ ϑ := by
                  dsimp only [i]
                  omega
                have h := congrFun hflat i
                simpa [i, flatV, hi, U₀, U₁, finMapTwoWords,
                  splitHalfRowWiseInterleavedWords] using h
            · intro hnested
              funext i
              by_cases hi : i.val < 2 ^ ϑ
              · have h := congrFun (congrFun hnested 0) ⟨i.val, hi⟩
                simpa [flatV, hi, U₀, U₁, finMapTwoWords,
                  splitHalfRowWiseInterleavedWords] using h
              · have hil := i.isLt
                have hisub : i.val - 2 ^ ϑ < 2 ^ ϑ := by
                  rw [pow_succ] at hil
                  omega
                have h := congrFun (congrFun hnested 1)
                  ⟨i.val - 2 ^ ϑ, hisub⟩
                simpa [flatV, hi, U₀, U₁, finMapTwoWords,
                  splitHalfRowWiseInterleavedWords] using h
          rw [hdist]
          exact hv_close