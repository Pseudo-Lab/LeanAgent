by
  classical
  intro ϑ
  induction ϑ with
  | zero =>
      intro h
      contradiction
  | succ ϑ_sub_1 ih =>
      cases ϑ_sub_1 with
      | zero =>
          simp only [zero_add, gt_iff_lt, zero_lt_one, ModuleCode, forall_const]
          intro u
          let h_affine := multilinearCombine₁_eq_affineLineEvaluation (F := F) (u := u)
          intro hprob
          simp_rw [h_affine] at hprob
          let h_uniform := prob_uniform_singleton_finFun_eq (F := F)
            (P := fun r => Δ₀(affineLineEvaluation (u 0) (u 1) r, MC) ≤ e)
          simp_rw [h_uniform, Nat.cast_one, ENNReal.coe_one, one_mul] at hprob
          have hCA := hC_proximityGapAffineLines (u 0) (u 1) hprob
          simp only [jointProximityNat₂, Fin.isValue] at hCA
          have hu : u = finMapTwoWords (u 0) (u 1) := by
            funext i
            match i with
            | 0 => rfl
            | 1 => rfl
          rw [hu.symm] at hCA
          exact hCA
      | succ ϑ_sub_2 =>
          intro _ u hprob
          set U₀ : Fin (2 ^ (ϑ_sub_2 + 1)) → Word A ι :=
            (splitHalfRowWiseInterleavedWords (ϑ := ϑ_sub_2 + 1) u).1
          set U₁ : Fin (2 ^ (ϑ_sub_2 + 1)) → Word A ι :=
            (splitHalfRowWiseInterleavedWords (ϑ := ϑ_sub_2 + 1) u).2
          unfold jointProximityNat
          simp only
          have h_snoc : ∀ r : Fin (ϑ_sub_2 + 1 + 1) → F,
              Fin.snoc (fun i : Fin (ϑ_sub_2 + 1) => r i.castSucc)
                (r (Fin.last (ϑ_sub_2 + 1))) = r := by
            intro r
            funext i
            by_cases hi : i = Fin.last (ϑ_sub_2 + 1)
            · simp only [hi, Fin.snoc_last]
            · have hi_val : i.val ≠ Fin.last (ϑ_sub_2 + 1) := by omega
              rw [Fin.val_last] at hi_val
              have hi_lt : i.val < ϑ_sub_2 + 1 := by omega
              simp only [Fin.snoc, Fin.castSucc_castLT, cast_eq, dite_eq_ite,
                ite_eq_left_iff, not_lt, isEmpty_Prop, hi_lt, IsEmpty.forall_iff]
          let P : F → (Fin (ϑ_sub_2 + 1) → F) → Prop := fun r_last r_init =>
            Δ₀(multilinearCombine (u := u) (r := Fin.snoc r_init r_last), MC) ≤ e
          let h_split := prob_split_last_uniform_sampling_of_finFun
            (ϑ := ϑ_sub_2 + 1) (F := F) (P := P)
          unfold P at h_split
          simp_rw [h_snoc] at h_split
          rw [h_split] at hprob
          have h_combine (r_init : Fin (ϑ_sub_2 + 1) → F) (r_last : F) :
              multilinearCombine u (Fin.snoc r_init r_last) =
                multilinearCombine (affineLineEvaluation U₀ U₁ r_last) r_init := by
            rw [multilinearCombine_recursive_form]
            simp only [Fin.snoc_last, Fin.init_snoc]
            rfl
          simp_rw [h_combine] at hprob
          let R := R_star_tensor MC (m := ϑ_sub_2 + 1) (e := e) (ε := ε) U₀ U₁
          have hR : Pr_{let r ← $ᵖ F}[r ∈ R] >
              (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            let h := prob_R_star_gt_threshold (MC := MC) (ε := ε)
              (ϑ := ϑ_sub_2 + 1) (u := u) (e := e) hprob
            exact h
          have hclose : ∀ r : R,
              jointProximityNat (u := affineLineEvaluation U₀ U₁ r.val)
                (e := e) (C := MC) := by
            intro r
            apply correlatedAgreement_of_mem_R_star_tensor
              (ih := fun u_prev => ih (by omega) u_prev) (u := u)
          let W₀ : InterleavedWord A (Fin (2 ^ (ϑ_sub_2 + 1))) ι := ⋈|U₀
          let W₁ : InterleavedWord A (Fin (2 ^ (ϑ_sub_2 + 1))) ι := ⋈|U₁
          have hline : Pr_{let r ← $ᵖ F}[
              Δ₀(affineLineEvaluation W₀ W₁ r,
                MC ^⋈ (Fin (2 ^ (ϑ_sub_2 + 1)))) ≤ e] >
              (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            apply lt_of_le_of_lt' _ hR
            apply Pr_le_Pr_of_implies
            intro r hr
            have h := hclose ⟨r, hr⟩
            unfold jointProximityNat at h
            exact h
          have hgap := h_interleaved_gaps (2 ^ (ϑ_sub_2 + 1)) Nat.one_le_two_pow
          have hfinal : jointProximityNat₂
              (u₀ := W₀) (u₁ := W₁) (e := e)
              (C := MC ^⋈ (Fin (2 ^ (ϑ_sub_2 + 1)))) := by
            apply hgap (u₀ := W₀) (u₁ := W₁)
            exact hline
          apply CA_split_rowwise_implies_CA (u := u) (e := e)
          exact hfinal