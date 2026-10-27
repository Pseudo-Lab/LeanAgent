by
  classical
  intro ϑ
  induction ϑ with
  | zero =>
      intro h
      contradiction
  | succ ϑ' ih =>
      cases ϑ' with
      | zero =>
          simp only [zero_add, gt_iff_lt, zero_lt_one, ModuleCode, forall_const]
          intro u hprob
          let hcombine := multilinearCombine₁_eq_affineLineEvaluation (F := F) (u := u)
          simp_rw [hcombine] at hprob
          let hprob_eq := prob_uniform_singleton_finFun_eq (F := F)
            (P := fun r => Δ₀(affineLineEvaluation (u 0) (u 1) r, MC) ≤ e)
          simp_rw [hprob_eq, Nat.cast_one, ENNReal.coe_one, one_mul] at hprob
          have hca := hC_proximityGapAffineLines (u 0) (u 1) hprob
          simp only [jointProximityNat₂, Fin.isValue] at hca
          have hu : u = finMapTwoWords (u 0) (u 1) := by
            funext i
            match i with
            | 0 => rfl
            | 1 => rfl
          rwa [← hu] at hca
      | succ k =>
          intro _ u hprob
          let t := k + 1
          set U₀ : Fin (2 ^ t) → Word A ι :=
            (splitHalfRowWiseInterleavedWords (ϑ := t) u).1
          set U₁ : Fin (2 ^ t) → Word A ι :=
            (splitHalfRowWiseInterleavedWords (ϑ := t) u).2
          unfold jointProximityNat
          simp only
          have hsnoc : ∀ r : Fin (t + 1) → F,
              Fin.snoc (fun i : Fin t => r i.castSucc) (r (Fin.last t)) = r := by
            intro r
            funext i
            by_cases hi : i = Fin.last t
            · simp only [hi, Fin.snoc_last]
            · have hiv : i.val ≠ Fin.last t := by omega
              rw [Fin.val_last] at hiv
              have hilt : i.val < t := by omega
              simp only [Fin.snoc, Fin.castSucc_castLT, cast_eq, dite_eq_ite,
                ite_eq_left_iff, not_lt, isEmpty_Prop, not_le, hilt, IsEmpty.forall_iff]
          let P : F → (Fin t → F) → Prop := fun rlast rinit =>
            Δ₀(multilinearCombine (u := u) (r := Fin.snoc rinit rlast), MC) ≤ e
          let hsplit := prob_split_last_uniform_sampling_of_finFun
            (ϑ := t) (F := F) (P := P)
          unfold P at hsplit
          simp_rw [hsnoc] at hsplit
          rw [hsplit] at hprob
          have hcombine (rinit : Fin t → F) (rlast : F) :
              multilinearCombine u (Fin.snoc rinit rlast) =
                multilinearCombine (affineLineEvaluation U₀ U₁ rlast) rinit := by
            rw [multilinearCombine_recursive_form]
            simp only [Fin.snoc_last, Fin.init_snoc]
            rfl
          simp_rw [hcombine] at hprob
          let R := R_star_tensor MC (m := t) (e := e) (ε := ε) U₀ U₁
          have hR : Pr_{let r ← $ᵖ F}[r ∈ R] >
              (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            exact prob_R_star_gt_threshold (MC := MC) (ε := ε) (ϑ := t)
              (u := u) (e := e) hprob
          have hclose : ∀ r : R,
              jointProximityNat (u := affineLineEvaluation U₀ U₁ r.val)
                (e := e) (C := MC) := by
            intro r
            apply correlatedAgreement_of_mem_R_star_tensor
              (ih := fun v => ih (by omega) v) (u := u)
          have hline :
              Pr_{let r ← $ᵖ F}[
                Δ₀(affineLineEvaluation
                    (u₀ := ⋈|(show WordStack A (Fin (2 ^ t)) ι from U₀))
                    (u₁ := ⋈|(show WordStack A (Fin (2 ^ t)) ι from U₁)) r,
                  MC ^⋈ (Fin (2 ^ t))) ≤ e] >
                (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            apply lt_of_le_of_lt' _ hR
            apply Pr_le_Pr_of_implies
            intro r hr
            have hr' := hclose ⟨r, hr⟩
            unfold jointProximityNat at hr'
            exact hr'
          have hgap := h_interleaved_gaps (2 ^ t) Nat.one_le_two_pow
          have hfinal : jointProximityNat₂
              (u₀ := ⋈|(show WordStack A (Fin (2 ^ t)) ι from U₀))
              (u₁ := ⋈|(show WordStack A (Fin (2 ^ t)) ι from U₁))
              (e := e) (C := MC ^⋈ (Fin (2 ^ t))) := by
            exact hgap
              (⋈|(show WordStack A (Fin (2 ^ t)) ι from U₀))
              (⋈|(show WordStack A (Fin (2 ^ t)) ι from U₁)) hline
          exact CA_split_rowwise_implies_CA (u := u) (e := e) hfinal