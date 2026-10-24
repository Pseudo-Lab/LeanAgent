by
  classical
  intro ϑ
  induction ϑ with
  | zero =>
      intro h
      contradiction
  | succ n ih =>
      cases n with
      | zero =>
          simp only [zero_add, gt_iff_lt, zero_lt_one, ModuleCode, forall_const]
          intro u
          let h_affine := multilinearCombine₁_eq_affineLineEvaluation (F := F) (u := u)
          intro hprob
          simp_rw [h_affine] at hprob
          let h_single := prob_uniform_singleton_finFun_eq (F := F)
            (P := fun r => Δ₀(affineLineEvaluation (u 0) (u 1) r, MC) ≤ e)
          simp_rw [h_single, Nat.cast_one, ENNReal.coe_one, one_mul] at hprob
          have hCA := hC_proximityGapAffineLines (u 0) (u 1) hprob
          simp only [jointProximityNat₂, Fin.isValue] at hCA
          have hu : u = finMapTwoWords (u 0) (u 1) := by
            funext i
            match i with
            | 0 => rfl
            | 1 => rfl
          rw [← hu] at hCA
          exact hCA
      | succ k =>
          intro _ u hprob
          set U₀ : Fin (2 ^ (k + 1)) → Word A ι :=
            (splitHalfRowWiseInterleavedWords (ϑ := k + 1) u).1
          set U₁ : Fin (2 ^ (k + 1)) → Word A ι :=
            (splitHalfRowWiseInterleavedWords (ϑ := k + 1) u).2
          unfold jointProximityNat
          simp only
          have h_snoc : ∀ r : Fin (k + 1 + 1) → F,
              Fin.snoc (fun i : Fin (k + 1) => r i.castSucc)
                (r (Fin.last (k + 1))) = r := by
            intro r
            funext i
            by_cases hi : i = Fin.last (k + 1)
            · simp only [hi, Fin.snoc_last]
            · have hi' : i.val ≠ Fin.last (k + 1) := by omega
              rw [Fin.val_last] at hi'
              have hlt : i.val < k + 1 := by omega
              simp only [Fin.snoc, Fin.castSucc_castLT, cast_eq, dite_eq_ite,
                ite_eq_left_iff, not_lt]
              simp only [isEmpty_Prop, not_le, hlt, IsEmpty.forall_iff]
          let P : F → (Fin (k + 1) → F) → Prop := fun r_last r_init =>
            Δ₀(multilinearCombine (u := u) (r := Fin.snoc r_init r_last), MC) ≤ e
          let hsplit := prob_split_last_uniform_sampling_of_finFun
            (ϑ := k + 1) (F := F) (P := P)
          unfold P at hsplit
          simp_rw [h_snoc] at hsplit
          rw [hsplit] at hprob
          let pred := k + 1
          have hcombine (r_init : Fin pred → F) (r_last : F) :
              multilinearCombine u (Fin.snoc r_init r_last) =
                multilinearCombine (affineLineEvaluation U₀ U₁ r_last) r_init := by
            rw [multilinearCombine_recursive_form]
            simp only [Fin.snoc_last, Fin.init_snoc]
            rfl
          simp_rw [hcombine] at hprob
          let R := R_star_tensor MC (m := pred) (e := e) (ε := ε) U₀ U₁
          have hRprob : Pr_{ let r ← $ᵖ F }[r ∈ R] >
              (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            exact prob_R_star_gt_threshold (MC := MC) (ε := ε) (ϑ := k + 1)
              (u := u) (e := e) hprob
          have hRcard : R.card > ε := by
            rw [prob_uniform_eq_card_filter_div_card] at hRprob
            simp only [ENNReal.coe_natCast] at hRprob
            rw [gt_iff_lt] at hRprob
            have hcancel := ENNReal.div_lt_div_iff_left
              (a := (ε : ENNReal))
              (b := (#(filter (fun r => r ∈ R) Finset.univ)))
              (c := (Fintype.card F : ENNReal))
              (hc₀ := by
                simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
                  not_false_eq_true])
              (hc := by
                simp only [ne_eq, ENNReal.natCast_ne_top, not_false_eq_true])
            rw [hcancel] at hRprob
            simp only [filter_univ_mem, Nat.cast_lt] at hRprob
            exact hRprob
          have hclose : ∀ r : R,
              jointProximityNat (u := affineLineEvaluation U₀ U₁ r.val)
                (e := e) (C := MC) := by
            intro r
            apply correlatedAgreement_of_mem_R_star_tensor
              (ih := fun u' => ih (by omega) u') (u := u)
          have hgap := h_interleaved_gaps (2 ^ (k + 1)) Nat.one_le_two_pow
          have hline :
              Pr_{ let r ← $ᵖ F }[
                Δ₀(affineLineEvaluation
                    (u₀ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₀))
                    (u₁ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₁)) r,
                  MC ^⋈ (Fin (2 ^ (k + 1)))) ≤ e] >
                (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            apply lt_of_le_of_lt' _ hRprob
            have himp : ∀ r : F, r ∈ R →
                Δ₀(affineLineEvaluation
                    (u₀ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₀))
                    (u₁ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₁)) r,
                  MC ^⋈ (Fin (2 ^ (k + 1))) ≤ e := by
              intro r hr
              have h := hclose ⟨r, hr⟩
              unfold jointProximityNat at h
              exact h
            have hle := Pr_le_Pr_of_implies (D := $ᵖ F)
              (f := fun r => r ∈ R)
              (g := fun r =>
                Δ₀(affineLineEvaluation
                    (u₀ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₀))
                    (u₁ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₁)) r,
                  MC ^⋈ (Fin (2 ^ (k + 1))) ≤ e)
              (h_imp := himp)
            simp only at hle
            exact hle
          have hfinal : jointProximityNat₂
              (u₀ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₀))
              (u₁ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₁))
              (e := e) (C := MC ^⋈ (Fin (2 ^ (k + 1))) := by
            exact hgap
              (u₀ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₀))
              (u₁ := ⋈|(show WordStack A (Fin (2 ^ (k + 1))) ι from U₁)) hline
          apply CA_split_rowwise_implies_CA (u := u) (e := e)
          exact hfinal