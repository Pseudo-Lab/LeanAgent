by
  classical
  intro ϑ
  induction ϑ with
  | zero =>
      intro h
      omega
  | succ ϑ_sub_1 ih =>
      cases ϑ_sub_1 with
      | zero =>
          simp only [zero_add, gt_iff_lt, zero_lt_one, ModuleCode, forall_const]
          intro u
          let h_eval := multilinearCombine₁_eq_affineLineEvaluation (F := F) (u := u)
          intro hprob
          simp_rw [h_eval] at hprob
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
            by_cases h : i = Fin.last (ϑ_sub_2 + 1)
            · simp only [h, Fin.snoc_last]
            · have hi : i.val ≠ Fin.last (ϑ_sub_2 + 1) := by omega
              rw [Fin.val_last] at hi
              have hi' : i.val < ϑ_sub_2 + 1 := by omega
              simp only [Fin.snoc, Fin.castSucc_castLT, cast_eq, dite_eq_ite,
                ite_eq_left_iff, not_lt]
              simp only [isEmpty_Prop, not_le, hi', IsEmpty.forall_iff]
          let P : F → (Fin (ϑ_sub_2 + 1) → F) → Prop := fun r_last r_init =>
            Δ₀(multilinearCombine (u := u) (r := Fin.snoc r_init r_last), MC) ≤ e
          let h_split := prob_split_last_uniform_sampling_of_finFun
            (ϑ := ϑ_sub_2 + 1) (F := F) (P := P)
          unfold P at h_split
          simp_rw [h_snoc] at h_split
          rw [h_split] at hprob
          let ϑ_pred := ϑ_sub_2 + 1
          have h_recursive (r_init : Fin ϑ_pred → F) (r_last : F) :
              multilinearCombine u (Fin.snoc r_init r_last) =
                multilinearCombine (affineLineEvaluation U₀ U₁ r_last) r_init := by
            rw [multilinearCombine_recursive_form]
            simp only [Fin.snoc_last, Fin.init_snoc]
            rfl
          simp_rw [h_recursive] at hprob
          let R_star_set := R_star_tensor MC (m := ϑ_pred) (e := e) (ε := ε) U₀ U₁
          have hR : Pr_{let r ← $ᵖ F}[r ∈ R_star_set] >
              (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            exact prob_R_star_gt_threshold (MC := MC) (ε := ε)
              (ϑ := ϑ_sub_2 + 1) (u := u) (e := e) hprob
          have hclose : ∀ r : R_star_set,
              jointProximityNat (u := affineLineEvaluation U₀ U₁ r.val)
                (e := e) (C := MC) := by
            intro r
            apply correlatedAgreement_of_mem_R_star_tensor
              (ih := fun u_prev => ih (by omega) u_prev) (u := u)
          have hline :
              Pr_{let r ← $ᵖ F}[
                Δ₀(affineLineEvaluation
                    (u₀ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₀))
                    (u₁ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₁)) r,
                  MC ^⋈ (Fin (2 ^ (ϑ_sub_2 + 1)))) ≤ e] >
                (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            apply lt_of_le_of_lt' _ hR
            have himp : ∀ r : F, r ∈ R_star_set →
                Δ₀(affineLineEvaluation
                    (u₀ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₀))
                    (u₁ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₁)) r,
                  MC ^⋈ (Fin (2 ^ (ϑ_sub_2 + 1)))) ≤ e := by
              intro r hr
              have h := hclose ⟨r, hr⟩
              unfold jointProximityNat at h
              exact h
            exact Pr_le_Pr_of_implies (D := $ᵖ F)
              (f := fun r => r ∈ R_star_set)
              (g := fun r =>
                Δ₀(affineLineEvaluation
                    (u₀ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₀))
                    (u₁ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₁)) r,
                  MC ^⋈ (Fin (2 ^ (ϑ_sub_2 + 1)))) ≤ e)
              himp
          have hgap := h_interleaved_gaps (2 ^ (ϑ_sub_2 + 1)) Nat.one_le_two_pow
          have hfinal : jointProximityNat₂
              (u₀ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₀))
              (u₁ := ⋈|(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1))) ι from U₁))
              (e := e) (C := MC ^⋈ (Fin (2 ^ (ϑ_sub_2 + 1))) := by
            exact hgap _ _ hline
          exact CA_split_rowwise_implies_CA (u := u) (e := e) hfinal