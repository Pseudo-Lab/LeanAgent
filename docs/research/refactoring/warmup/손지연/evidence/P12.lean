theorem interleaved_affine_gaps_imply_tensor_gaps
    (hC_proximityGapAffineLines : e_ε_correlatedAgreementAffineLinesNat
      (F := F) (A := A) (ι := ι) (C := MC) (e := e) (ε := ε))
    (h_interleaved_gaps : ∀ m : ℕ, m ≥ 1 →
      e_ε_correlatedAgreementAffineLinesNat (F := F)
        (A := InterleavedSymbol A (Fin m)) (ι := ι) (C := MC ^⋈ (Fin m)) e ε) :
    ∀ (ϑ : ℕ), (hϑ_gt_0 : ϑ > 0) → δ_ε_multilinearCorrelatedAgreement_Nat (F := F) (A := A)
      (ι := ι) (C := MC) (ϑ := ϑ) (e := e) (ε := ε) := by
  classical
  have tensor_success_split {n : ℕ}
      (u : WordStack A (Fin (2 ^ (n + 1))) ι) :
      Pr_{let r ← $ᵖ (Fin (n + 1) → F)}[Δ₀(multilinearCombine u r, MC) ≤ e] =
      Pr_{let r_last ← $ᵖ F; let r_init ← $ᵖ (Fin n → F)}[
        multilinearCombine_affineComb_split_last_close (MC := MC) u e r_last r_init] := by
    classical
    have fold (r : Fin (n + 1) → F) :
        (Δ₀(multilinearCombine u r, MC) ≤ e) =
          multilinearCombine_affineComb_split_last_close (MC := MC) u e
            (r (Fin.last n)) (fun i => r i.castSucc) := by
      unfold multilinearCombine_affineComb_split_last_close
      rw [multilinearCombine_recursive_form]
      rfl
    simp_rw [fold]
    exact prob_split_last_uniform_sampling_of_finFun _


  have tensor_gap_one
      (hC : e_ε_correlatedAgreementAffineLinesNat (F := F) (A := A) (ι := ι) (C := MC) e ε) :
      δ_ε_multilinearCorrelatedAgreement_Nat (F := F) (A := A) (ι := ι) (C := MC) 1 e ε := by
    classical
    intro u hprob
    simp_rw [multilinearCombine₁_eq_affineLineEvaluation (F := F) (u := u)] at hprob
    simp_rw [prob_uniform_singleton_finFun_eq (F := F)
      (P := fun r => Δ₀(affineLineEvaluation (u 0) (u 1) r, MC) ≤ e),
      Nat.cast_one, ENNReal.coe_one, one_mul] at hprob
    have hCA := hC (u 0) (u 1) hprob
    have hu : u = finMapTwoWords (u 0) (u 1) := by
      funext i
      fin_cases i <;> rfl
    simpa only [jointProximityNat₂, ← hu] using hCA


  have tensor_gap_succ {n : ℕ}
      (ih : δ_ε_multilinearCorrelatedAgreement_Nat (F := F) (A := A) (ι := ι) (C := MC) n e ε)
      (hGaps : ∀ m : ℕ, m ≥ 1 → e_ε_correlatedAgreementAffineLinesNat (F := F)
        (A := InterleavedSymbol A (Fin m)) (ι := ι) (C := MC ^⋈ (Fin m)) e ε) :
      δ_ε_multilinearCorrelatedAgreement_Nat (F := F) (A := A) (ι := ι) (C := MC) (n + 1) e ε := by
    classical
    intro u hprob
    let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := n) u).1
    let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := n) u).2
    let good := R_star_tensor MC (m := n) (e := e) (ε := ε) U₀ U₁
    have hgood : Pr_{let r ← $ᵖ F}[r ∈ good] >
        (ε : ENNReal) / (Fintype.card F : ENNReal) := by
      apply prob_R_star_gt_threshold (MC := MC) (u := u) (e := e)
      rwa [← tensor_success_split (u := u)]
    have hclose : ∀ r : F, r ∈ good →
        Δ₀(affineLineEvaluation (⋈|U₀) (⋈|U₁) r, MC ^⋈ (Fin (2 ^ n))) ≤ e := by
      intro r hr
      exact correlatedAgreement_of_mem_R_star_tensor (MC := MC) (ih := ih) (u := u) ⟨r, hr⟩
    apply CA_split_rowwise_implies_CA (C := MC) (u := u) (e := e)
    apply hGaps (2 ^ n) Nat.one_le_two_pow (⋈|U₀) (⋈|U₁)
    exact lt_of_lt_of_le hgood (Pr_le_Pr_of_implies (D := $ᵖ F) (h_imp := hclose))

  intro ϑ
  induction ϑ with
  | zero => intro h; omega
  | succ n ih =>
    cases n with
    | zero => intro _; exact tensor_gap_one hC_proximityGapAffineLines
    | succ n =>
      intro _
      exact tensor_gap_succ (ih (Nat.succ_pos n)) h_interleaved_gaps
