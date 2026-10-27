# 웜업 15문제 블록 트리 분석

토큰은 공식 `proof_length` 규칙. 확인 = 루트 서브트리 토큰 + `:= by` 줄 토큰이 공식 값과 같은지.

| # | 정리 | 공식 | 확인 | 노드 수 | 확정 중복 그룹 | 반복 토큰 합 | 근사 중복 쌍 |
| ---: | --- | ---: | --- | ---: | ---: | ---: | ---: |
| 1 | `substOldPostSubset` | 313 | OK | 91 | 1 | 20 | 0 |
| 2 | `extractedOldExprInVars` | 222 | OK | 77 | 0 | 0 | 0 |
| 3 | `InitsUpdatesComm` | 224 | OK | 46 | 0 | 0 | 0 |
| 4 | `fundamental_theorem_of_variational_calculus'` | 851 | OK | 80 | 0 | 0 | 0 |
| 5 | `time_deriv_time_deriv_electricField_of_isExtrema` | 1,372 | OK | 116 | 0 | 0 | 0 |
| 6 | `ι_timeOrderF_superCommuteF_eq_time` | 1,217 | OK | 110 | 3 | 226 | 0 |
| 7 | `progress` | 408 | OK | 82 | 0 | 0 | 0 |
| 8 | `parallelReduction_diamond` | 407 | OK | 63 | 0 | 0 | 0 |
| 9 | `bisimilarity_congr_choice` | 251 | OK | 60 | 0 | 0 | 0 |
| 10 | `fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius` | 1,463 | OK | 141 | 1 | 28 | 0 |
| 11 | `fold_advances_evaluation_poly` | 1,906 | OK | 149 | 4 | 123 | 3 |
| 12 | `interleaved_affine_gaps_imply_tensor_gaps` | 1,353 | OK | 125 | 2 | 142 | 0 |
| 13 | `putnam_1964_a4` | 1,769 | OK | 174 | 4 | 104 | 4 |
| 14 | `putnam_1964_b2` | 1,754 | OK | 267 | 5 | 136 | 2 |
| 15 | `putnam_1995_a3` | 4,085 | OK | 232 | 4 | 1,075 | 1 |

반복 토큰 = (개수 − 1) × 블록 토큰. 같은 증명을 한 번만 쓰면 없어지는 토큰이며, 보조정리 호출 비용은 빼지 않은 값이다.

## 1. `CallElimCorrect.substOldPostSubset` (313 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 52–71 | 0 | `case app ih1 ih2 =>` | 71 | 22.7% |
| 72–85 | 0 | `case quant trih eih =>` | 62 | 19.8% |
| 34–51 | 0 | `case ite cih tih eih =>` | 59 | 18.8% |
| 86–97 | 0 | `case eq ih1 ih2 =>` | 41 | 13.1% |
| 61–71 | 1 | `. simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.…` | 37 | 11.8% |
| 75–81 | 1 | `. apply List.Subset.trans` | 36 | 11.5% |
| 54–60 | 1 | `. split` | 28 | 8.9% |
| 7–14 | 0 | `case fvar =>` | 20 | 6.4% |

확정 중복 그룹 (이름 정규화 후 해시 일치)

| 개수 | 블록 토큰 | 반복 토큰 | 위치와 첫 줄 |
| ---: | ---: | ---: | --- |
| 2 | 20 | 20 | src 7–14 `case fvar =>`<br>src 15–21 `case op =>` |

## 2. `CallElimCorrect.extractedOldExprInVars` (222 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 11–38 | 0 | `case app fn e fn_ih e_ih =>` | 77 | 34.7% |
| 56–71 | 0 | `case ite cih tih eih =>` | 45 | 20.3% |
| 42–55 | 0 | `case quant trih eih =>` | 40 | 18.0% |
| 26–38 | 1 | `. cases Hnorm with` | 34 | 15.3% |
| 72–82 | 0 | `case eq ih1 ih2 =>` | 31 | 14.0% |
| 17–25 | 1 | `. next Hfalse =>` | 23 | 10.4% |
| 7–10 | 0 | `induction post <;>` | 16 | 7.2% |
| 8–9 | 1 | `simp [Imperative.HasVarsPure.getVars, extractOldExprVars,` | 11 | 5.0% |

## 3. `Core.InitsUpdatesComm` (224 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 24–55 | 0 | `case update_some σ x v σ₀ xs vs σ₁ Hup Hups ih =>` | 165 | 73.7% |
| 31–55 | 1 | `. apply UpdateStates.update_some (σ':=updatedStates σ₀ ks' …` | 126 | 56.2% |
| 32–52 | 2 | `. simp [UpdateStateUpdated Hup, updatedStates]` | 95 | 42.4% |
| 34–45 | 3 | `. have Hdef := UpdateStateDefined' Hup` | 53 | 23.7% |
| 46–52 | 3 | `. rw [List.unzip_zip] <;> simp_all` | 29 | 12.9% |
| 16–23 | 0 | `case update_none =>` | 23 | 10.3% |
| 53–55 | 2 | `. apply (ih Hinit ?_ ?_).2.2` | 20 | 8.9% |
| 26–30 | 1 | `. apply updatedStatesInit Hlen1` | 18 | 8.0% |

## 4. `fundamental_theorem_of_variational_calculus'` (851 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 28–43 | 0 | `have inner_pos₂ : ∀ x (hx : x ∈ Metric.ball x₀ δ₂), 0 < (⟪f…` | 178 | 20.9% |
| 49–62 | 0 | `have bump_exists : ∃ φ : Y → ℝ, IsTestFunction φ ∧ φ x₀ > 0…` | 149 | 17.5% |
| 52–62 | 1 | `(∀ x ∈ Metric.closedBall x₀ (δ₂/4), 0 < φ x) := by` | 107 | 12.6% |
| 110–120 | 0 | `have closedBall_subset_support :` | 79 | 9.3% |
| 96–102 | 0 | `have h_nonneg : ∀ x, 0 ≤ φ x * ⟪f x, f x₀⟫_ℝ := by` | 53 | 6.2% |
| 40–41 | 1 | `have inner_eq_self_add_diff : ⟪f₂ x, x₂⟫_ℝ = ⟪x₂, x₂⟫_ℝ + ⟪…` | 36 | 4.2% |
| 123–125 | 0 | `have integral_pos : 0 < ∫ x, φ x * ⟪f x, f x₀⟫_ℝ ∂μ :=` | 36 | 4.2% |
| 57–59 | 2 | `refine ⟨φ1.toFun, ⟨φ1.contDiff, φ1.hasCompactSupport⟩,` | 35 | 4.1% |

## 5. `Electromagnetism.ElectromagneticPotential.time_deriv_time_deriv_electricField_of_isExtrema` (1,372 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 20–126 | 0 | `calc _` | 1,213 | 88.4% |
| 80–126 | 1 | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electr…` | 538 | 39.2% |
| 99–121 | 2 | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕…` | 163 | 11.9% |
| 31–40 | 1 | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∂ₜ (fun t => ∑ j, ∂[j] (A.magneticF…` | 116 | 8.5% |
| 86–94 | 2 | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electr…` | 114 | 8.3% |
| 67–76 | 1 | `_ = (1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.elect…` | 113 | 8.2% |
| 21–30 | 1 | `_= ∂ₜ (fun t =>` | 97 | 7.1% |
| 77–79 | 1 | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electr…` | 94 | 6.9% |

## 6. `FieldSpecification.WickAlgebra.ι_timeOrderF_superCommuteF_eq_time` (1,217 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 10–112 | 0 | `· rintro x ⟨φs, rfl⟩` | 1,114 | 91.5% |
| 17–107 | 1 | `· rintro x ⟨φs', rfl⟩` | 989 | 81.3% |
| 19–95 | 2 | `calc _` | 855 | 70.3% |
| 41–69 | 3 | `_ = crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs) •` | 362 | 29.7% |
| 70–81 | 3 | `_ = crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs) •` | 163 | 13.4% |
| 82–95 | 3 | `_ = crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs) •` | 152 | 12.5% |
| 71–80 | 4 | `(ι (ofCrAnListF (List.takeWhile (fun c => ¬crAnTimeOrderRel…` | 140 | 11.5% |
| 52–61 | 4 | `ι (ofCrAnListF (List.takeWhile (fun c => ¬crAnTimeOrderRel …` | 119 | 9.8% |

확정 중복 그룹 (이름 정규화 후 해시 일치)

| 개수 | 블록 토큰 | 반복 토큰 | 위치와 첫 줄 |
| ---: | ---: | ---: | --- |
| 8 | 23 | 161 | src 44–45 `ι (ofCrAnListF (List.filter (fun c =>`<br>src 47–48 `ι (ofCrAnListF (List.filter (fun c =>`<br>src 54–55 `ι (ofCrAnListF (List.filter (fun c =>`<br>src 57–58 `ι (ofCrAnListF (List.filter (fun c =>`<br>src 73–74 `ι (ofCrAnListF (List.filter (fun c => (crAnTimeOr…`<br>src 77–78 `ι (ofCrAnListF (List.filter (fun c => (crAnTimeOr…`<br>src 85–86 `ι (ofCrAnListF (List.filter (fun c => (crAnTimeOr…`<br>src 88–89 `ι (ofCrAnListF (List.filter (fun c => (crAnTimeOr…` |
| 2 | 35 | 35 | src 79–80 `ι (ofCrAnListF (List.filter (fun c => (crAnTimeOr…`<br>src 90–91 `ι (ofCrAnListF (List.filter (fun c => (crAnTimeOr…` |
| 2 | 30 | 30 | src 64–64 `rw [crAnTimeOrderList, show φs' ++ φ :: ψ :: φs =…`<br>src 67–67 `rw [crAnTimeOrderList, show φs' ++ ψ :: φ :: φs =…` |

## 7. `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress` (408 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 6–22 | 0 | `case app t₁ _ _ t₂ l r ih_l ih_r =>` | 79 | 19.4% |
| 61–70 | 0 | `case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>` | 70 | 17.2% |
| 23–34 | 0 | `case tapp σ' der _ ih =>` | 53 | 13.0% |
| 9–18 | 1 | `&#124; inl val_l =>` | 46 | 11.3% |
| 35–44 | 0 | `case let' t₁ σ t₂ τ L der _ ih _ =>` | 44 | 10.8% |
| 45–52 | 0 | `case inl der _ ih =>` | 35 | 8.6% |
| 53–60 | 0 | `case inr der _ ih =>` | 35 | 8.6% |
| 64–66 | 1 | `&#124; inl val =>` | 31 | 7.6% |

## 8. `Cslib.SKI.parallelReduction_diamond` (407 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 5–31 | 0 | `case par a a' b b' ha' hb' =>` | 160 | 39.3% |
| 50–64 | 0 | `case red_S a b c =>` | 104 | 25.6% |
| 40–49 | 0 | `case red_K c =>` | 67 | 16.5% |
| 32–39 | 0 | `case red_I =>` | 55 | 13.5% |
| 55–63 | 1 | `case par d c' hd hc =>` | 53 | 13.0% |
| 25–31 | 1 | `case red_S a c =>` | 45 | 11.1% |
| 10–16 | 1 | `case par a'' b'' ha'' hb'' =>` | 42 | 10.3% |
| 43–47 | 1 | `case par a' c' ha hc =>` | 32 | 7.9% |

## 9. `Cslib.CCS.bisimilarity_congr_choice` (251 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 36–62 | 0 | `case right =>` | 116 | 46.2% |
| 9–35 | 0 | `case left =>` | 115 | 45.8% |
| 12–27 | 1 | `case choice p q r hbisim =>` | 70 | 27.9% |
| 39–54 | 1 | `case choice p q r hbisim =>` | 70 | 27.9% |
| 55–62 | 1 | `case bisim hbisim =>` | 38 | 15.1% |
| 28–35 | 1 | `case bisim hbisim =>` | 37 | 14.7% |
| 15–21 | 2 | `case choiceL a b c htr =>` | 33 | 13.1% |
| 42–48 | 2 | `case choiceL a b c htr =>` | 33 | 13.1% |

## 10. `Binius.BinaryBasefold.fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius` (1,463 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 52–147 | 0 | `have h_dist_le_fw_dist_times_fiber_size : (hammingDist f g'…` | 721 | 49.3% |
| 73–114 | 1 | `have h_ΔH_subset_bad_fiber_points : ΔH ⊆ Finset.biUnion Y_b…` | 364 | 24.9% |
| 120–141 | 1 | `· -- The size of the sum is the number of bad fibers (`Y_ba…` | 170 | 11.6% |
| 85–104 | 2 | `have h_elemenet_Y_bad : y_of_x ∈ Y_bad.toFinset := by` | 148 | 10.1% |
| 169–178 | 0 | `have h_algebraic_identity : (d_i_plus_steps - 1) * 2 ^ step…` | 143 | 9.8% |
| 30–49 | 0 | `obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw` | 109 | 7.5% |
| 127–134 | 2 | `have h_card_fiber_of_each_y : ∀ y ∈ Y_bad.toFinset,` | 102 | 7.0% |
| 192–200 | 0 | `have h_final_inequality : 2 * d_H_nat ≤ d_i - 1 := by` | 96 | 6.6% |

확정 중복 그룹 (이름 정규화 후 해시 일치)

| 개수 | 블록 토큰 | 반복 토큰 | 위치와 첫 줄 |
| ---: | ---: | ---: | --- |
| 2 | 28 | 28 | src 173–174 `rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (…`<br>src 176–177 `rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (…` |

## 11. `Binius.BinaryBasefold.fold_advances_evaluation_poly` (1,906 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 142–184 | 0 | `calc f_i_plus_1 y` | 538 | 28.2% |
| 69–111 | 0 | `have h_fiber_diff : x₁.val - x₀.val = 1 := by` | 429 | 22.5% |
| 156–184 | 1 | `_ = P_i_plus_1.eval y.val := by` | 293 | 15.4% |
| 32–47 | 0 | `set new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>` | 187 | 9.8% |
| 120–124 | 0 | `set P₁_coeffs := fun j : Fin (2^(ℓ - (i + 1))) => coeffs ⟨j…` | 126 | 6.6% |
| 115–119 | 0 | `set P₀_coeffs := fun j : Fin (2^(ℓ - (i + 1))) => coeffs ⟨j…` | 124 | 6.5% |
| 33–41 | 1 | `(1 - r_chal) * (coeffs ⟨j.val * 2, by` | 114 | 6.0% |
| 172–176 | 2 | `conv_lhs => enter [1]; rw [mul_comm (a := Polynomial.C (coe…` | 95 | 5.0% |

확정 중복 그룹 (이름 정규화 후 해시 일치)

| 개수 | 블록 토큰 | 반복 토큰 | 위치와 첫 줄 |
| ---: | ---: | ---: | --- |
| 2 | 36 | 36 | src 118–118 `have h3 : 2^(ℓ - (i + 1)) * 2 = 2^(ℓ - (i + 1) + …`<br>src 123–123 `have h3 : 2^(ℓ - (i + 1)) * 2 = 2^(ℓ - (i + 1) + …` |
| 2 | 34 | 34 | src 52–53 `have h_res := is_fiber_iff_generates_quotient_poi…`<br>src 60–61 `have h_res := is_fiber_iff_generates_quotient_poi…` |
| 2 | 30 | 30 | src 117–117 `have h2 : 2^(ℓ - (i + 1) + 1) = 2^(ℓ - i) := by r…`<br>src 122–122 `have h2 : 2^(ℓ - (i + 1) + 1) = 2^(ℓ - i) := by r…` |
| 2 | 23 | 23 | src 130–131 `simp only [h_P_i_eval, Fin.eta, Polynomial.eval_a…`<br>src 133–134 `simp only [h_P_i_eval, Fin.eta, Polynomial.eval_a…` |

근사 중복 쌍 (편집 거리 DP 정렬)

| 블록 A | 블록 B | 토큰 | 유사도 | 다른 토큰 (A → B, 횟수) |
| --- | --- | --- | ---: | --- |
| src 115–119 `set P₀_coeffs := fun j : Fin (2^(ℓ - (i ` | src 120–124 `set P₁_coeffs := fun j : Fin (2^(ℓ - (i ` | 124·126 | 0.984 | `P₀_coeffs`→`P₁_coeffs` 1 |
| src 48–54 `have h_eval_qMap_x₀ : (AdditiveNTT.qMap ` | src 56–62 `have h_eval_qMap_x₁ : (AdditiveNTT.qMap ` | 82·82 | 0.988 | `x₀`→`x₁` 2, `h_eval_qMap_x₀`→`h_eval_qMap_x₁` 1, `x₀.val`→`x₁.val` 1 |
| src 79–85 `have h_cast_0 :` | src 86–93 `have h_cast_1 :` | 77·79 | 0.949 | `0`→`1` 2, `h_cast_0`→`h_cast_1` 1 |

## 12. `interleaved_affine_gaps_imply_tensor_gaps` (1,353 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 15–177 | 0 | `&#124; succ ϑ_sub_1 ih =>` | 1,340 | 99.0% |
| 37–177 | 1 | `&#124; succ ϑ_sub_2 =>` | 1,188 | 87.8% |
| 143–167 | 2 | `have h_prob_line_gt_eps_div_q :` | 354 | 26.2% |
| 148–167 | 3 | `] > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by` | 258 | 19.1% |
| 51–63 | 2 | `have h_finsnoc_eq_r: ∀ r: Fin (ϑ_sub_2 + 1 + 1) → F,` | 151 | 11.2% |
| 17–36 | 1 | `&#124; zero =>` | 144 | 10.6% |
| 169–175 | 2 | `have h_final_gap : jointProximityNat₂` | 141 | 10.4% |
| 120–132 | 2 | `have h_R_star_card_gt_eps : R_star_set.card > ε := by` | 116 | 8.6% |

확정 중복 그룹 (이름 정규화 후 해시 일치)

| 개수 | 블록 토큰 | 반복 토큰 | 위치와 첫 줄 |
| ---: | ---: | ---: | --- |
| 4 | 26 | 78 | src 153–153 `(u₀ := ⋈&#124;(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1…`<br>src 162–162 `(u₀ := ⋈&#124;(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1…`<br>src 170–170 `(u₀ := ⋈&#124;(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1…`<br>src 174–174 `(u₁ := ⋈&#124;(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1…` |
| 3 | 32 | 64 | src 146–146 `(u₁ := ⋈&#124;(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1…`<br>src 154–154 `(u₁ := ⋈&#124;(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1…`<br>src 163–163 `(u₁ := ⋈&#124;(show WordStack A (Fin (2 ^ (ϑ_sub_2 + 1…` |

## 13. `putnam_1964_a4` (1,769 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 63–184 | 0 | `have h_periodic : ∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u…` | 1,239 | 70.0% |
| 65–163 | 1 | `have h₁ : ∀ m : ℕ, u (i + m) = u (j + m) := by` | 1,027 | 58.1% |
| 67–162 | 2 | `have h₂ : ∀ m : ℕ, u (i + m) = u (j + m) := by` | 999 | 56.5% |
| 70–162 | 3 | `&#124; h m ih =>` | 969 | 54.8% |
| 94–162 | 4 | `&#124; m + 4 =>` | 879 | 49.7% |
| 6–61 | 0 | `have h_main : ∃ (i j : ℕ), i < j ∧ (u i = u j ∧ u (i + 1) =…` | 527 | 29.8% |
| 8–60 | 1 | `have h₁ : ∃ (i j : ℕ), i < j ∧ (u i = u j ∧ u (i + 1) = u (…` | 449 | 25.4% |
| 13–35 | 2 | `have h₂ : Set.Finite (Set.range f) := by` | 191 | 10.8% |

확정 중복 그룹 (이름 정규화 후 해시 일치)

| 개수 | 블록 토큰 | 반복 토큰 | 위치와 첫 줄 |
| ---: | ---: | ---: | --- |
| 2 | 27 | 27 | src 117–118 `have h₆ : (i + (m + 4) - 1 : ℕ) = i + (m + 3) := …`<br>src 125–126 `have h₁₀ : (j + (m + 4) - 1 : ℕ) = j + (m + 3) :=…` |
| 2 | 27 | 27 | src 119–120 `have h₇ : (i + (m + 4) - 2 : ℕ) = i + (m + 2) := …`<br>src 127–128 `have h₁₁ : (j + (m + 4) - 2 : ℕ) = j + (m + 2) :=…` |
| 2 | 27 | 27 | src 121–122 `have h₈ : (i + (m + 4) - 3 : ℕ) = i + (m + 1) := …`<br>src 129–130 `have h₁₂ : (j + (m + 4) - 3 : ℕ) = j + (m + 1) :=…` |
| 2 | 23 | 23 | src 123–124 `have h₉ : (i + (m + 4) - 4 : ℕ) = i + m := by`<br>src 131–132 `have h₁₃ : (j + (m + 4) - 4 : ℕ) = j + m := by` |

근사 중복 쌍 (편집 거리 DP 정렬)

| 블록 A | 블록 B | 토큰 | 유사도 | 다른 토큰 (A → B, 횟수) |
| --- | --- | --- | ---: | --- |
| src 98–105 `have h₄ : u (i + (m + 4)) = ((u (i + (m ` | src 106–116 `have h₅ : u (j + (m + 4)) = ((u (j + (m ` | 167·178 | 0.916 | `i`→`j` 10, `h₆`→`h₇` 2, `h₄`→`h₅` 1, `h₅`→`h₆` 1, `h₅.1`→`h₆.1` 1 |
| src 133–136 `have h₁₄ : u (i + (m + 3)) = u (j + (m +` | src 137–140 `have h₁₅ : u (i + (m + 2)) = u (j + (m +` | 48·48 | 0.938 | `3`→`2` 3, `h₁₅`→`h₁₆` 2, `h₁₄`→`h₁₅` 1 |
| src 133–136 `have h₁₄ : u (i + (m + 3)) = u (j + (m +` | src 141–144 `have h₁₆ : u (i + (m + 1)) = u (j + (m +` | 48·48 | 0.938 | `3`→`1` 3, `h₁₅`→`h₁₇` 2, `h₁₄`→`h₁₆` 1 |
| src 137–140 `have h₁₅ : u (i + (m + 2)) = u (j + (m +` | src 141–144 `have h₁₆ : u (i + (m + 1)) = u (j + (m +` | 48·48 | 0.938 | `2`→`1` 3, `h₁₆`→`h₁₇` 2, `h₁₅`→`h₁₆` 1 |

## 14. `putnam_1964_b2` (1,754 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 140–292 | 0 | `have h_card : P.card = 2 ^ (Fintype.card S - 1) := by` | 875 | 49.9% |
| 14–126 | 0 | `have h_subset_or_compl : ∀ (A : Set S), A ∈ P ∨ Aᶜ ∈ P := by` | 746 | 42.5% |
| 145–211 | 1 | `have h₁ : P.card = Q.card := by` | 313 | 17.8% |
| 20–55 | 1 | `have h₃ : ∃ (U : Set S), U ∈ P ∧ A ∩ U = ∅ := by` | 256 | 14.6% |
| 57–92 | 1 | `have h₄ : ∃ (V : Set S), V ∈ P ∧ Aᶜ ∩ V = ∅ := by` | 256 | 14.6% |
| 213–258 | 1 | `have h₂ : P.card + Q.card = 2 ^ Fintype.card S := by` | 242 | 13.8% |
| 271–291 | 1 | `have h₅ : P.card = 2 ^ (Fintype.card S - 1) := by` | 214 | 12.2% |
| 214–245 | 2 | `have h₃ : P.card + Q.card = (Finset.univ : Finset (Set S)).…` | 188 | 10.7% |

확정 중복 그룹 (이름 정규화 후 해시 일치)

| 개수 | 블록 토큰 | 반복 토큰 | 위치와 첫 줄 |
| ---: | ---: | ---: | --- |
| 2 | 48 | 48 | src 97–104 `have h₅ : U ⊆ Aᶜ := by`<br>src 105–112 `have h₆ : V ⊆ A := by` |
| 2 | 28 | 28 | src 48–52 `have h₉ : A ∩ U = ∅ := by`<br>src 85–89 `have h₉ : Aᶜ ∩ V = ∅ := by` |
| 2 | 20 | 20 | src 30–33 `have h₉ : A ∩ U = U ∩ A := by`<br>src 67–70 `have h₁₀ : Aᶜ ∩ U = U ∩ Aᶜ := by` |
| 2 | 20 | 20 | src 34–38 `have h₁₀ : U ∩ A ≠ ∅ := by`<br>src 71–75 `have h₁₁ : U ∩ Aᶜ ≠ ∅ := by` |
| 2 | 20 | 20 | src 174–174 `have h₆ : ∀ (A : Set S), A ∈ P → Aᶜ ∈ Q := h₂`<br>src 175–175 `have h₇ : ∀ (A : Set S), A ∈ Q → Aᶜ ∈ P := h₃` |

근사 중복 쌍 (편집 거리 DP 정렬)

| 블록 A | 블록 B | 토큰 | 유사도 | 다른 토큰 (A → B, 횟수) |
| --- | --- | --- | ---: | --- |
| src 21–40 `have h₄ : ¬(A ∉ P ∧ ∀ (U : Set S), U ∈ P` | src 58–77 `have h₅ : ¬(Aᶜ ∉ P ∧ ∀ (U : Set S), U ∈ ` | 139·139 | 0.986 | `A`→`Aᶜ` 7, `h₆`→`h₇` 2, `h₇`→`h₈` 2, `h₈`→`h₉` 2, `h₁₀`→`h₁₁` 2, `h₄`→`h₅` 1, `h₅`→`h₆` 1, `h₅.1`→`h₆.1` 1 |
| src 42–53 `· have h₆ : ¬(∀ (U : Set S), U ∈ P → A ∩` | src 79–90 `· have h₇ : ¬(∀ (U : Set S), U ∈ P → Aᶜ ` | 86·86 | 0.919 | `U`→`V` 4, `h₆`→`h₇` 3, `A`→`Aᶜ` 3, `h₇`→`h₈` 2, `hU`→`hV` 2, `h₄`→`h₅` 1, `h₅`→`h₆` 1 |

## 15. `putnam_1995_a3` (4,085 토큰, OK)

큰 노드 (서브트리 토큰 순)

| src 줄 | 깊이 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | ---: | ---: |
| 7–281 | 0 | `have h_main : ∀ (d e f : (Fin 9 → ℤ)), ((relation d e) ∧ (r…` | 4,082 | 99.9% |
| 116–189 | 1 | `have h₇ : 7 ∣ digits_to_num e + digits_to_num d := by` | 1,160 | 28.4% |
| 18–65 | 1 | `have h₅ : ∀ (i : Fin 9), 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : …` | 812 | 19.9% |
| 67–114 | 1 | `have h₆ : ∀ (i : Fin 9), 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : …` | 812 | 19.9% |
| 21–55 | 2 | `have h₇ : (digits_to_num (fun j : Fin 9 => if j = i then e …` | 619 | 15.2% |
| 70–104 | 2 | `have h₈ : (digits_to_num (fun j : Fin 9 => if j = i then f …` | 619 | 15.2% |
| 150–188 | 2 | `have h₁₃ : 7 ∣ digits_to_num e + digits_to_num d := by` | 585 | 14.3% |
| 22–55 | 3 | `calc` | 570 | 14.0% |

확정 중복 그룹 (이름 정규화 후 해시 일치)

| 개수 | 블록 토큰 | 반복 토큰 | 위치와 첫 줄 |
| ---: | ---: | ---: | --- |
| 2 | 812 | 812 | src 18–65 `have h₅ : ∀ (i : Fin 9), 7 ∣ (e i - d i) * (10 : …`<br>src 67–114 `have h₆ : ∀ (i : Fin 9), 7 ∣ (f i - e i) * (10 : …` |
| 4 | 30 | 90 | src 193–193 `have h₉ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + …`<br>src 194–194 `have h₁₀ : 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) +…`<br>src 200–200 `have h₁₃ : 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) +…`<br>src 213–213 `have h₁₅ : 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) +…` |
| 4 | 30 | 90 | src 229–229 `have h₁₂ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i …`<br>src 246–246 `have h₁₆ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i …`<br>src 251–251 `have h₁₉ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i …`<br>src 255–255 `have h₂₂ : (7 : ℤ) ∣ (f i - d i) * (10 : ℤ) ^ (i …` |
| 2 | 83 | 83 | src 11–13 `have h₃ : ∀ (i : Fin 9), 7 ∣ (digits_to_num (fun …`<br>src 14–16 `have h₄ : ∀ (i : Fin 9), 7 ∣ (digits_to_num (fun …` |

근사 중복 쌍 (편집 거리 DP 정렬)

| 블록 A | 블록 B | 토큰 | 유사도 | 다른 토큰 (A → B, 횟수) |
| --- | --- | --- | ---: | --- |
| src 158–158 `have h₁₈ : (∑ i : Fin 9, (e i - d i) * (` | src 176–176 `have h₂₃ : (∑ i : Fin 9, (e i - d i) * (` | 71·78 | 0.872 | `h₁₈`→`h₂₃` 1, `9`→`2` 1, `)`→`=` 1, `=`→`(` 1 |
