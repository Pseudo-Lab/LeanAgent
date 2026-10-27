# Warm-up 블록 분석

proof token은 공식 `proof_length` 규칙. 각 문제의 블록 합 + `:= by` 줄 토큰 = 공식 값인지 확인함.
src 줄은 benchmark JSONL `src` 필드 기준 줄 번호. 깊이 0은 증명 최상위, 1 이상은 감싸는 블록 안으로 내려가 나눈 블록.

| # | 문제 | 출처 | 공식 | 확인 | 블록 수 | 가장 큰 블록 | 비중 | 반복 후보 | case 후보 |
| ---: | --- | --- | ---: | --- | ---: | --- | ---: | ---: | ---: |
| 1 | `substOldPostSubset` | strata | 313 | OK | 10 | `case app ih1 ih2 =>` (src 52–71) | 22.7% | 0 | 2 |
| 2 | `extractedOldExprInVars` | strata | 222 | OK | 7 | `case app fn e fn_ih e_ih =>` (src 11–38) | 34.7% | 0 | 0 |
| 3 | `InitsUpdatesComm` | strata | 224 | OK | 8 | `case update_some σ x v σ₀ xs vs σ₁ Hup` (src 24–55) | 73.7% | 0 | 0 |
| 4 | `fundamental_theorem_of_variational_calculus'` | physlib | 851 | OK | 27 | `have inner_pos₂ : ∀ x (hx : x ∈ Metric` (src 28–43) | 20.9% | 0 | 0 |
| 5 | `time_deriv_time_deriv_electricField_of_isExtrema` | physlib | 1,372 | OK | 12 | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fu` (src 80–126) | 39.2% | 0 | 0 |
| 6 | `ι_timeOrderF_superCommuteF_eq_time` | physlib | 1,217 | OK | 24 | `calc _` (src 19–95) | 70.3% | 3 | 0 |
| 7 | `progress` | cslib | 408 | OK | 13 | `case app t₁ _ _ t₂ l r ih_l ih_r =>` (src 6–22) | 19.4% | 0 | 9 |
| 8 | `parallelReduction_diamond` | cslib | 407 | OK | 7 | `case par a a' b b' ha' hb' =>` (src 5–31) | 39.3% | 0 | 7 |
| 9 | `bisimilarity_congr_choice` | cslib | 251 | OK | 8 | `case right =>` (src 36–62) | 46.2% | 1 | 5 |
| 10 | `fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius` | arklib | 1,463 | OK | 23 | `have h_dist_le_fw_dist_times_fiber_siz` (src 52–147) | 49.3% | 0 | 0 |
| 11 | `fold_advances_evaluation_poly` | arklib | 1,906 | OK | 25 | `calc f_i_plus_1 y` (src 142–184) | 28.2% | 4 | 0 |
| 12 | `interleaved_affine_gaps_imply_tensor_gaps` | arklib | 1,353 | OK | 33 | `have h_prob_line_gt_eps_div_q :` (src 143–167) | 26.2% | 1 | 0 |
| 13 | `putnam_1964_a4` | putnambench | 1,769 | OK | 3 | `have h_periodic : ∃ N c : ℕ, c > 0 ∧ ∀` (src 63–184) | 70.0% | 4 | 4 |
| 14 | `putnam_1964_b2` | putnambench | 1,754 | OK | 5 | `have h_card : P.card = 2 ^ (Fintype.ca` (src 140–292) | 49.9% | 3 | 0 |
| 15 | `putnam_1995_a3` | putnambench | 4,085 | OK | 14 | `have h₇ : 7 ∣ digits_to_num e + digits` (src 116–189) | 28.4% | 2 | 0 |

## 유형별 묶음

블록 종류(`case` 분기, `calc` 단계, `have` 계열)별 토큰 비중이 50% 이상인 종류로 유형을 정함.

| 유형 | 문제 | 분할 규칙 |
| --- | --- | --- |
| 분기형 | 1, 2, 3, 7, 8, 9 | `case`·`&#124; tag =>` 분기 하나를 블록으로 봄. 큰 분기 안의 분기(`cases` 안 `case`)는 한 단계 더 나눔. 분기 본문끼리 비교함. |
| 계산 연쇄형 | 5, 6 | `calc`의 단계 하나(`_ = …`와 그 근거)를 블록으로 봄. 큰 `calc` 블록은 단계 단위로 한 단계 더 나눔. |
| 중간 명제형 | 4, 10, 11, 12, 13, 14, 15 | `have` 하나와 그 증명을 블록으로 봄. 감싸는 `have`는 안으로 내려가고, 큰 `have`는 안쪽 `have` 단위로 한 단계 더 나눔. 사용되지 않는 `have`는 Lean 린터로 찾음. |

| # | 유형 | case | calc | have | 기타 |
| ---: | --- | ---: | ---: | ---: | ---: |
| 1 | 분기형 | 97.4% | 0% | 0% | 2.2% |
| 2 | 분기형 | 91.4% | 0% | 0% | 8.1% |
| 3 | 분기형 | 83.9% | 0% | 9.4% | 6.2% |
| 4 | 중간 명제형 | 0% | 0% | 95.1% | 4.8% |
| 5 | 계산 연쇄형 | 0% | 81.2% | 11.5% | 7.1% |
| 6 | 계산 연쇄형 | 0% | 70.3% | 10.2% | 18.2% |
| 7 | 분기형 | 94.1% | 0% | 2.2% | 3.4% |
| 8 | 분기형 | 97.8% | 0% | 0% | 2.0% |
| 9 | 분기형 | 92.0% | 0% | 0% | 7.6% |
| 10 | 중간 명제형 | 0% | 0% | 93.9% | 6.0% |
| 11 | 중간 명제형 | 0% | 28.2% | 71.1% | 0.6% |
| 12 | 중간 명제형 | 11.1% | 0% | 84.3% | 3.9% |
| 13 | 중간 명제형 | 0% | 0% | 99.8% | 0.1% |
| 14 | 중간 명제형 | 0% | 0% | 99.8% | 0.1% |
| 15 | 중간 명제형 | 0% | 0% | 98.5% | 0.3% |

## 1. `CallElimCorrect.substOldPostSubset` (strata, 313 토큰, OK, 분기형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 6–6 | 0 | block | `induction post <;> simp [substOld]` | 7 | 2.2% |
| 7–14 | 0 | block | `case fvar =>` | 20 | 6.4% |
| 15–21 | 0 | block | `case op =>` | 20 | 6.4% |
| 22–26 | 0 | block | `case const =>` | 13 | 4.2% |
| 27–31 | 0 | block | `case bvar =>` | 13 | 4.2% |
| 32–33 | 0 | block | `case abs ih =>` | 6 | 1.9% |
| 34–51 | 0 | block | `case ite cih tih eih =>` | 59 | 18.8% |
| 52–71 | 0 | block | `case app ih1 ih2 =>` | 71 | 22.7% |
| 72–85 | 0 | block | `case quant trih eih =>` | 62 | 19.8% |
| 86–97 | 0 | block | `case eq ih1 ih2 =>` | 41 | 13.1% |

비슷한 case 본문 후보 (본문 토큰 ≥ 8, 유사도 ≥ 0.85):

- src 7 `case fvar =>` (17) ↔ src 15 `case op =>` (17), 유사도 1.0
- src 22 `case const =>` (10) ↔ src 27 `case bvar =>` (10), 유사도 1.0

## 2. `CallElimCorrect.extractedOldExprInVars` (strata, 222 토큰, OK, 분기형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 6–6 | 0 | block | `intros Hnorm` | 2 | 0.9% |
| 7–10 | 0 | block | `induction post <;>` | 16 | 7.2% |
| 11–38 | 0 | block | `case app fn e fn_ih e_ih =>` | 77 | 34.7% |
| 39–41 | 0 | block | `case abs ih =>` | 10 | 4.5% |
| 42–55 | 0 | block | `case quant trih eih =>` | 40 | 18.0% |
| 56–71 | 0 | block | `case ite cih tih eih =>` | 45 | 20.3% |
| 72–82 | 0 | block | `case eq ih1 ih2 =>` | 31 | 14.0% |

## 3. `Core.InitsUpdatesComm` (strata, 224 토큰, OK, 분기형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 10–10 | 0 | block | `intros Hup Hinit` | 3 | 1.3% |
| 11–11 | 0 | block | `exists (updatedStates σ ks' vs')` | 7 | 3.1% |
| 12–12 | 0 | block | `have Hk : (isDefined σ' ks) := UpdateStatesDefined Hup` | 11 | 4.9% |
| 13–13 | 0 | block | `have Hlen1 := InitStatesLength Hinit` | 5 | 2.2% |
| 14–14 | 0 | block | `have Hlen2 := UpdateStatesLength Hup` | 5 | 2.2% |
| 15–15 | 0 | block | `induction Hup generalizing σ''` | 4 | 1.8% |
| 16–23 | 0 | block | `case update_none =>` | 23 | 10.3% |
| 24–55 | 0 | block | `case update_some σ x v σ₀ xs vs σ₁ Hup Hups ih =>` | 165 | 73.7% |

src 24–55 블록(73.7%)을 한 단계 더 나눔:

| src 줄 | 종류 | 첫 줄 | 토큰 | 비중 |
| --- | --- | --- | ---: | ---: |
| 25–25 | other | `refine ⟨rfl, ?_, ?_⟩` | 8 | 3.6% |
| 26–30 | other | `. apply updatedStatesInit Hlen1` | 18 | 8.0% |
| 31–55 | other | `. apply UpdateStates.update_some (σ':=updatedStates σ₀ ks' vs')` | 126 | 56.2% |

## 4. `fundamental_theorem_of_variational_calculus'` (physlib, 851 토큰, OK, 중간 명제형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 7–7 | 0 | block | `rw [funext_iff]; by_contra h₀` | 7 | 0.8% |
| 8–8 | 0 | block | `obtain ⟨x₀, hx0⟩ := not_forall.1 h₀` | 9 | 1.1% |
| 9–9 | 0 | block | `simp at hx0 -- hx0 : f x₀ ≠ 0` | 3 | 0.4% |
| 13–13 | 0 | block | `let f₂ : Y → WithLp 2 V := toL2 ℝ ∘ f` | 13 | 1.5% |
| 14–14 | 0 | block | `let x₂ := f₂ x₀` | 5 | 0.6% |
| 16–17 | 0 | block | `have hx2 : x₂ ≠ 0 := by` | 21 | 2.5% |
| 19–19 | 0 | block | `have hcont₂ : ContinuousAt f₂ x₀ := ((toL2 ℝ).continuous.comp hf).con…` | 16 | 1.9% |
| 24–24 | 0 | block | `obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=` | 9 | 1.1% |
| 25–26 | 0 | block | `Metric.continuousAt_iff.mp hcont₂ (‖x₂‖ / 2)` | 21 | 2.5% |
| 28–43 | 0 | block | `have inner_pos₂ : ∀ x (hx : x ∈ Metric.ball x₀ δ₂), 0 < (⟪f₂ x, x₂⟫_ℝ…` | 178 | 20.9% |
| 45–45 | 0 | block | `have inner_pos_V : ∀ x ∈ Metric.ball x₀ δ₂, 0 < ⟪f x, f x₀⟫_ℝ := fun …` | 28 | 3.3% |
| 49–62 | 0 | block | `have bump_exists : ∃ φ : Y → ℝ, IsTestFunction φ ∧ φ x₀ > 0 ∧` | 149 | 17.5% |
| 63–64 | 0 | block | `obtain ⟨φ, hφ_testfun, hφ_pos_x₀, hφ_non_neg, hφ_support_subset, hφ_p…` | 16 | 1.9% |
| 66–66 | 0 | block | `let g : Y → V := fun x => φ x • f x₀` | 15 | 1.8% |
| 68–68 | 0 | block | `have hg_test : IsTestFunction g := IsTestFunction.smul_right hφ_testf…` | 9 | 1.1% |
| 72–72 | 0 | block | `have key_integral := hg g hg_test` | 6 | 0.7% |
| 74–74 | 0 | block | `simp only [g, inner_smul_right'] at key_integral` | 9 | 1.1% |
| 81–82 | 0 | block | `have support_subset : Function.support φ ⊆ Metric.ball x₀ δ₂ :=` | 18 | 2.1% |
| 83–86 | 0 | block | `have supp_subset2 : Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) ⊆…` | 35 | 4.1% |
| 87–88 | 0 | block | `have hinner_cont : Continuous (fun x => ⟪f x, f x₀⟫_ℝ) :=` | 35 | 4.1% |
| 89–93 | 0 | block | `have integrable_prod :` | 32 | 3.8% |
| 96–102 | 0 | block | `have h_nonneg : ∀ x, 0 ≤ φ x * ⟪f x, f x₀⟫_ℝ := by` | 53 | 6.2% |
| 106–107 | 0 | block | `have hμ_ball : 0 < μ (Metric.ball x₀ (δ₂/4)) :=` | 25 | 2.9% |
| 108–109 | 0 | block | `have hμ : 0 < μ (Metric.closedBall x₀ (δ₂/4)) :=` | 22 | 2.6% |
| 110–120 | 0 | block | `have closedBall_subset_support :` | 79 | 9.3% |
| 123–125 | 0 | block | `have integral_pos : 0 < ∫ x, φ x * ⟪f x, f x₀⟫_ℝ ∂μ :=` | 36 | 4.2% |
| 126–126 | 0 | block | `linarith` | 1 | 0.1% |

## 5. `Electromagnetism.ElectromagneticPotential.time_deriv_time_deriv_electricField_of_isExtrema` (physlib, 1,372 토큰, OK, 계산 연쇄형)

감싸는 블록 안으로 내려가서 나눔: `calc _`

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 10–11 | 0 | block | `have hEs : ∀ j, ContDiff ℝ 2 (fun y => A.electricField 𝓕.c t y j) :=` | 37 | 2.7% |
| 12–13 | 0 | block | `have hEd : ∀ j k, Differentiable ℝ (∂[k] (fun y => A.electricField 𝓕.…` | 36 | 2.6% |
| 14–17 | 0 | block | `have hBt : ∀ j, Differentiable ℝ` | 59 | 4.3% |
| 18–19 | 0 | block | `have hJt : Differentiable ℝ (fun s => J.currentDensity 𝓕.c s x i) :=` | 26 | 1.9% |
| 20–20 | 0 | wrapper | `calc _` | 2 | 0.1% |
| 21–30 | 1 | block | `_= ∂ₜ (fun t =>` | 97 | 7.1% |
| 31–40 | 1 | block | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∂ₜ (fun t => ∑ j, ∂[j] (A.magneticFieldMatrix…` | 116 | 8.5% |
| 41–47 | 1 | block | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ((∑ j, ∂ₜ (fun t => ∂[j] (A.magneticFieldMatr…` | 86 | 6.3% |
| 48–56 | 1 | block | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * (∑ j, ∂[j] (fun x => ∂ₜ (A.magneticFieldMatri…` | 77 | 5.6% |
| 57–66 | 1 | block | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) *(∑ j, ∂[j] (fun x => ∂[j] (A.electricField 𝓕.c…` | 90 | 6.6% |
| 67–76 | 1 | block | `_ = (1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕…` | 113 | 8.2% |
| 77–79 | 1 | block | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.…` | 94 | 6.9% |
| 80–126 | 1 | block | `_ = 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (fun x => ∂[j] (A.electricField 𝓕.…` | 538 | 39.2% |

## 6. `FieldSpecification.WickAlgebra.ι_timeOrderF_superCommuteF_eq_time` (physlib, 1,217 토큰, OK, 계산 연쇄형)

감싸는 블록 안으로 내려가서 나눔: `· rintro x ⟨φs, rfl⟩` → `· rintro x ⟨φs', rfl⟩`

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 5–7 | 0 | block | `let pb (b : 𝓕.FieldOpFreeAlgebra) (hc : b ∈ Submodule.span ℂ (Set.ran…` | 57 | 4.7% |
| 8–8 | 0 | block | `change pb b (Basis.mem_span _ b)` | 8 | 0.7% |
| 9–9 | 0 | block | `apply Submodule.span_induction` | 2 | 0.2% |
| 10–10 | 0 | wrapper | `· rintro x ⟨φs, rfl⟩` | 8 | 0.7% |
| 11–11 | 1 | block | `simp only [ofListBasis_eq_ofList, map_mul, pb]` | 9 | 0.7% |
| 12–14 | 1 | block | `let pa (a : 𝓕.FieldOpFreeAlgebra) (hc : a ∈ Submodule.span ℂ (Set.ran…` | 59 | 4.8% |
| 15–15 | 1 | block | `change pa a (Basis.mem_span _ a)` | 8 | 0.7% |
| 16–16 | 1 | block | `apply Submodule.span_induction` | 2 | 0.2% |
| 17–17 | 1 | wrapper | `· rintro x ⟨φs', rfl⟩` | 8 | 0.7% |
| 18–18 | 2 | block | `simp only [ofListBasis_eq_ofList, map_mul, pa]` | 9 | 0.7% |
| 19–95 | 2 | block | `calc _` | 855 | 70.3% |
| 96–96 | 2 | block | `rw [Subalgebra.mem_center_iff.mp (ι_superCommuteF_ofCrAnOpF_ofCrAnOpF…` | 9 | 0.7% |
| 97–97 | 2 | block | `repeat rw [mul_assoc]` | 5 | 0.4% |
| 98–99 | 2 | block | `rw [← map_mul, ← map_mul, ← map_mul, ← ofCrAnListF_append, ← ofCrAnLi…` | 20 | 1.6% |
| 100–100 | 2 | block | `have h1 := insertionSort_of_takeWhile_filter 𝓕.crAnTimeOrderRel φ φs'…` | 8 | 0.7% |
| 101–101 | 2 | block | `simp [decide_not, Bool.decide_and, List.append_assoc, List.cons_appen…` | 13 | 1.1% |
| 102–102 | 2 | block | `rw [← h1, ← crAnTimeOrderList]` | 8 | 0.7% |
| 103–103 | 2 | block | `by_cases hq : (𝓕 &#124;>ₛ φ) ≠ (𝓕 &#124;>ₛ ψ)` | 18 | 1.5% |
| 104–104 | 2 | block | `· simp [ι_superCommuteF_of_diff_statistic hq]` | 6 | 0.5% |
| 105–107 | 2 | block | `· rw [crAnTimeOrderSign, Wick.koszulSign_eq_rel_eq_stat _ _ hφψ hψφ (…` | 30 | 2.5% |
| 108–108 | 1 | block | `· simp only [map_mul, zero_mul, map_zero, mul_zero, pa]` | 14 | 1.2% |
| 109–110 | 1 | block | `· intro x y hx hy hpx hpy` | 16 | 1.3% |
| 111–112 | 1 | block | `· intro x hx hpx` | 9 | 0.7% |
| 113–113 | 0 | block | `· simp only [map_mul, mul_zero, map_zero, pb]` | 12 | 1.0% |
| 114–115 | 0 | block | `· intro x y hx hy hpx hpy` | 14 | 1.2% |
| 116–117 | 0 | block | `· intro x hx hpx` | 9 | 0.7% |

src 19–95 블록(70.3%)을 한 단계 더 나눔:

| src 줄 | 종류 | 첫 줄 | 토큰 | 비중 |
| --- | --- | --- | ---: | ---: |
| 21–32 | calc | `_ = crAnTimeOrderSign (φs' ++ φ :: ψ :: φs) •` | 107 | 8.8% |
| 34–39 | calc | `_ = crAnTimeOrderSign (φs' ++ φ :: ψ :: φs) •` | 69 | 5.7% |
| 41–69 | calc | `_ = crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs) •` | 362 | 29.7% |
| 70–81 | calc | `_ = crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs) •` | 163 | 13.4% |
| 82–95 | calc | `_ = crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs) •` | 152 | 12.5% |

반복 논증 후보 (이름을 정규화한 토큰열 유사도 ≥ 0.9, 후보일 뿐 동일성 증명 아님):

- src 52–61 `ι (ofCrAnListF (List.takeWhile (fun c => ¬crAnTim…` (119) ↔ src 83–91 `(ι (ofCrAnListF (List.takeWhile (fun c => ¬crAnTi…` (119), 유사도 0.958
- src 42–50 `(ι (ofCrAnListF (List.takeWhile (fun c => ¬crAnTi…` (117) ↔ src 52–61 `ι (ofCrAnListF (List.takeWhile (fun c => ¬crAnTim…` (119), 유사도 0.958
- src 42–50 `(ι (ofCrAnListF (List.takeWhile (fun c => ¬crAnTi…` (117) ↔ src 83–91 `(ι (ofCrAnListF (List.takeWhile (fun c => ¬crAnTi…` (119), 유사도 0.958

## 7. `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress` (cslib, 408 토큰, OK, 분기형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 2–2 | 0 | block | `generalize eq : [] = Γ at der` | 9 | 2.2% |
| 3–3 | 0 | block | `have der' : Typing Γ t τ := der` | 9 | 2.2% |
| 4–4 | 0 | block | `induction der <;> subst eq` | 5 | 1.2% |
| 5–5 | 0 | block | `case var mem => grind` | 5 | 1.2% |
| 6–22 | 0 | block | `case app t₁ _ _ t₂ l r ih_l ih_r =>` | 79 | 19.4% |
| 23–34 | 0 | block | `case tapp σ' der _ ih =>` | 53 | 13.0% |
| 35–44 | 0 | block | `case let' t₁ σ t₂ τ L der _ ih _ =>` | 44 | 10.8% |
| 45–52 | 0 | block | `case inl der _ ih =>` | 35 | 8.6% |
| 53–60 | 0 | block | `case inr der _ ih =>` | 35 | 8.6% |
| 61–70 | 0 | block | `case case t₁ _ _ t₂ _ t₃ _ der _ _ ih _ _ =>` | 70 | 17.2% |
| 71–71 | 0 | block | `case sub => grind` | 4 | 1.0% |
| 72–77 | 0 | block | `case abs σ _ τ L _ _=>` | 31 | 7.6% |
| 78–83 | 0 | block | `case tabs L _ _=>` | 28 | 6.9% |

비슷한 case 본문 후보 (본문 토큰 ≥ 8, 유사도 ≥ 0.85):

- src 15 `&#124; inr red_r =>` (12) ↔ src 31 `&#124; inr red =>` (13), 유사도 0.88
- src 19 `&#124; inr red_l =>` (12) ↔ src 31 `&#124; inr red =>` (13), 유사도 0.88
- src 19 `&#124; inr red_l =>` (12) ↔ src 41 `&#124; inr red =>` (12), 유사도 0.917
- src 19 `&#124; inr red_l =>` (12) ↔ src 67 `&#124; inr red =>` (13), 유사도 0.88
- src 31 `&#124; inr red =>` (13) ↔ src 41 `&#124; inr red =>` (12), 유사도 0.88
- src 41 `&#124; inr red =>` (12) ↔ src 67 `&#124; inr red =>` (13), 유사도 0.88
- src 45 `case inl der _ ih =>` (29) ↔ src 53 `case inr der _ ih =>` (29), 유사도 0.966
- src 48 `&#124; inr red =>` (13) ↔ src 56 `&#124; inr red =>` (13), 유사도 0.923
- src 72 `case abs σ _ τ L _ _=>` (22) ↔ src 78 `case tabs L _ _=>` (22), 유사도 0.955

## 8. `Cslib.SKI.parallelReduction_diamond` (cslib, 407 토큰, OK, 분기형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 2–2 | 0 | block | `intro a a₁ a₂ h₁ h₂` | 6 | 1.5% |
| 3–3 | 0 | block | `cases h₁` | 2 | 0.5% |
| 4–4 | 0 | block | `case refl => exact ⟨a₂, h₂, .refl a₂⟩` | 12 | 2.9% |
| 5–31 | 0 | block | `case par a a' b b' ha' hb' =>` | 160 | 39.3% |
| 32–39 | 0 | block | `case red_I =>` | 55 | 13.5% |
| 40–49 | 0 | block | `case red_K c =>` | 67 | 16.5% |
| 50–64 | 0 | block | `case red_S a b c =>` | 104 | 25.6% |

비슷한 case 본문 후보 (본문 토큰 ≥ 8, 유사도 ≥ 0.85):

- src 20 `case red_K =>` (25) ↔ src 43 `case par a' c' ha hc =>` (25), 유사도 0.88
- src 34 `case refl => use a₁; exact ⟨.refl a₁, .…` (11) ↔ src 39 `case red_I => use a₁; exact ⟨.refl a₁, …` (11), 유사도 0.909
- src 34 `case refl => use a₁; exact ⟨.refl a₁, .…` (11) ↔ src 42 `case refl => use a₁; exact ⟨.refl a₁, .…` (12), 유사도 0.87
- src 34 `case refl => use a₁; exact ⟨.refl a₁, .…` (11) ↔ src 48 `case red_K =>` (11), 유사도 0.909
- src 39 `case red_I => use a₁; exact ⟨.refl a₁, …` (11) ↔ src 42 `case refl => use a₁; exact ⟨.refl a₁, .…` (12), 유사도 0.87
- src 39 `case red_I => use a₁; exact ⟨.refl a₁, …` (11) ↔ src 48 `case red_K =>` (11), 유사도 1.0
- src 42 `case refl => use a₁; exact ⟨.refl a₁, .…` (12) ↔ src 48 `case red_K =>` (11), 유사도 0.87

## 9. `Cslib.CCS.bisimilarity_congr_choice` (cslib, 251 토큰, OK, 분기형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 3–3 | 0 | block | `intro h` | 2 | 0.8% |
| 4–4 | 0 | block | `exists @ChoiceBisim _ _ defs` | 6 | 2.4% |
| 5–5 | 0 | block | `constructor` | 1 | 0.4% |
| 6–6 | 0 | block | `· constructor; assumption` | 4 | 1.6% |
| 7–7 | 0 | block | `intro s1 s2 r μ` | 5 | 2.0% |
| 8–8 | 0 | block | `constructor` | 1 | 0.4% |
| 9–35 | 0 | block | `case left =>` | 115 | 45.8% |
| 36–62 | 0 | block | `case right =>` | 116 | 46.2% |

src 9–35 블록(45.8%)을 한 단계 더 나눔:

| src 줄 | 종류 | 첫 줄 | 토큰 | 비중 |
| --- | --- | --- | ---: | ---: |
| 10–10 | other | `intro s1' htr` | 3 | 1.2% |
| 11–11 | other | `cases r` | 2 | 0.8% |
| 12–27 | case | `case choice p q r hbisim =>` | 70 | 27.9% |
| 28–35 | case | `case bisim hbisim =>` | 37 | 14.7% |

src 36–62 블록(46.2%)을 한 단계 더 나눔:

| src 줄 | 종류 | 첫 줄 | 토큰 | 비중 |
| --- | --- | --- | ---: | ---: |
| 37–37 | other | `intro s2' htr` | 3 | 1.2% |
| 38–38 | other | `cases r` | 2 | 0.8% |
| 39–54 | case | `case choice p q r hbisim =>` | 70 | 27.9% |
| 55–62 | case | `case bisim hbisim =>` | 38 | 15.1% |

반복 논증 후보 (이름을 정규화한 토큰열 유사도 ≥ 0.9, 후보일 뿐 동일성 증명 아님):

- src 9–35 `case left =>` (115) ↔ src 36–62 `case right =>` (116), 유사도 0.978

비슷한 case 본문 후보 (본문 토큰 ≥ 8, 유사도 ≥ 0.85):

- src 9 `case left =>` (112) ↔ src 36 `case right =>` (113), 유사도 0.978
- src 12 `case choice p q r hbisim =>` (63) ↔ src 39 `case choice p q r hbisim =>` (63), 유사도 0.984
- src 15 `case choiceL a b c htr =>` (26) ↔ src 42 `case choiceL a b c htr =>` (26), 유사도 0.962
- src 22 `case choiceR a b c htr =>` (11) ↔ src 49 `case choiceR a b c htr =>` (11), 유사도 1.0
- src 28 `case bisim hbisim =>` (33) ↔ src 55 `case bisim hbisim =>` (34), 유사도 0.955

## 10. `Binius.BinaryBasefold.fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius` (arklib, 1,463 토큰, OK, 중간 명제형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 7–7 | 0 | block | `unfold fiberwiseClose at h_fw_dist_lt` | 4 | 0.3% |
| 8–8 | 0 | block | `unfold hammingClose` | 2 | 0.1% |
| 10–10 | 0 | block | `let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f` | 14 | 1.0% |
| 11–11 | 0 | block | `let C_i := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by o…` | 19 | 1.3% |
| 12–12 | 0 | block | `let d_H := Code.distFromCode f C_i` | 6 | 0.4% |
| 13–13 | 0 | block | `let d_i := BBF_CodeDistance ℓ 𝓡 (⟨i, by omega⟩)` | 14 | 1.0% |
| 14–14 | 0 | block | `let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i.val + steps, by omega⟩` | 14 | 1.0% |
| 16–23 | 0 | block | `have h_d_i_gt_0 : d_i > 0 := by` | 90 | 6.2% |
| 25–27 | 0 | block | `have h_C_i_nonempty : Nonempty C_i := by` | 32 | 2.2% |
| 30–49 | 0 | block | `obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw` | 109 | 7.5% |
| 52–147 | 0 | block | `have h_dist_le_fw_dist_times_fiber_size : (hammingDist f g' : ℕ∞) ≤ d…` | 721 | 49.3% |
| 150–159 | 0 | block | `have h_dist_bridge : d_H ≤ d_fw * 2 ^ steps := by` | 57 | 3.9% |
| 163–165 | 0 | block | `have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 := by` | 18 | 1.2% |
| 169–178 | 0 | block | `have h_algebraic_identity : (d_i_plus_steps - 1) * 2 ^ steps = d_i - …` | 143 | 9.8% |
| 182–185 | 0 | block | `have h_dH_ne_top : d_H ≠ ⊤ := by` | 24 | 1.6% |
| 188–188 | 0 | block | `let d_H_nat := ENat.toNat d_H` | 5 | 0.3% |
| 189–189 | 0 | block | `have h_dH_eq : d_H = d_H_nat := (ENat.coe_toNat h_dH_ne_top).symm` | 12 | 0.8% |
| 192–200 | 0 | block | `have h_final_inequality : 2 * d_H_nat ≤ d_i - 1 := by` | 96 | 6.6% |
| 202–202 | 0 | block | `simp only [d_H, d_H_nat] at h_dH_eq` | 9 | 0.6% |
| 204–204 | 0 | block | `rw [h_dH_eq]` | 4 | 0.3% |
| 206–206 | 0 | block | `change ((2 : ℕ) : ℕ∞) * ↑Δ₀(f, C_i).toNat < ↑(BBF_CodeDistance ℓ 𝓡 ⟨↑…` | 34 | 2.3% |
| 207–207 | 0 | block | `rw [←ENat.coe_mul, ENat.coe_lt_coe]` | 7 | 0.5% |
| 208–209 | 0 | block | `apply Nat.lt_of_le_pred (n := 2 * Δ₀(f, C_i).toNat) (m := d_i) (h := …` | 28 | 1.9% |

src 52–147 블록(49.3%)을 한 단계 더 나눔:

| src 줄 | 종류 | 첫 줄 | 토큰 | 비중 |
| --- | --- | --- | ---: | ---: |
| 56–56 | other | `change (Δ₀(f, g') : ℕ∞) ≤ ↑d_fw * ((2 ^ steps : ℕ) : ℕ∞)` | 28 | 1.9% |
| 57–57 | other | `rw [←ENat.coe_mul, ENat.coe_le_coe, h_g'_min_card]` | 9 | 0.6% |
| 59–59 | have | `set ΔH := Finset.filter (fun x => f x ≠ g' x) Finset.univ` | 15 | 1.0% |
| 60–61 | have | `have h_dist_eq_card : hammingDist f g' = ΔH.card := by` | 19 | 1.3% |
| 62–62 | other | `rw [h_dist_eq_card]` | 4 | 0.3% |
| 64–64 | have | `set Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g'` | 11 | 0.8% |
| 65–65 | other | `simp only at * -- simplify domain indices everywhere` | 4 | 0.3% |
| 69–69 | have | `have hFinType_Y_bad : Fintype Y_bad := by exact Fintype.ofFinite ↑Y_b…` | 11 | 0.8% |
| 73–114 | have | `have h_ΔH_subset_bad_fiber_points : ΔH ⊆ Finset.biUnion Y_bad.toFinset` | 364 | 24.9% |
| 117–117 | other | `apply (Finset.card_le_card h_ΔH_subset_bad_fiber_points).trans` | 6 | 0.4% |
| 119–119 | other | `rw [Finset.card_biUnion]` | 4 | 0.3% |
| 120–141 | other | `· -- The size of the sum is the number of bad fibers (`Y_bad.ncard`) …` | 170 | 11.6% |
| 142–147 | other | `· -- Prove that the fibers for distinct quotient points y₁, y₂ are di…` | 57 | 3.9% |

## 11. `Binius.BinaryBasefold.fold_advances_evaluation_poly` (arklib, 1,906 토큰, OK, 중간 명제형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 25–25 | 0 | block | `simp only` | 2 | 0.1% |
| 26–26 | 0 | block | `intro y` | 2 | 0.1% |
| 27–28 | 0 | block | `set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := …` | 35 | 1.8% |
| 29–29 | 0 | block | `set x₀ := fiberMap 0` | 5 | 0.3% |
| 30–30 | 0 | block | `set x₁ := fiberMap 1` | 5 | 0.3% |
| 31–31 | 0 | block | `set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, b…` | 18 | 0.9% |
| 32–47 | 0 | block | `set new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>` | 187 | 9.8% |
| 48–54 | 0 | block | `have h_eval_qMap_x₀ : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₀.v…` | 82 | 4.3% |
| 56–62 | 0 | block | `have h_eval_qMap_x₁ : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₁.v…` | 82 | 4.3% |
| 63–64 | 0 | block | `have hx₀ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)` | 20 | 1.0% |
| 65–66 | 0 | block | `have hx₁ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)` | 20 | 1.0% |
| 67–67 | 0 | block | `simp only [Fin.isValue] at hx₀ hx₁` | 8 | 0.4% |
| 69–111 | 0 | block | `have h_fiber_diff : x₁.val - x₀.val = 1 := by` | 429 | 22.5% |
| 112–113 | 0 | block | `set P_i_plus_1 :=` | 20 | 1.0% |
| 115–119 | 0 | block | `set P₀_coeffs := fun j : Fin (2^(ℓ - (i + 1))) => coeffs ⟨j.val * 2, …` | 124 | 6.5% |
| 120–124 | 0 | block | `set P₁_coeffs := fun j : Fin (2^(ℓ - (i + 1))) => coeffs ⟨j.val * 2 +…` | 126 | 6.6% |
| 125–125 | 0 | block | `set P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate i coeffs` | 9 | 0.5% |
| 126–126 | 0 | block | `set P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate i coeffs` | 9 | 0.5% |
| 127–127 | 0 | block | `have h_P_i_eval := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate…` | 14 | 0.7% |
| 129–131 | 0 | block | `have h_equation_39_x₀ : P_i.eval x₀.val = P₀.eval y.val + x₀.val * P₁…` | 38 | 2.0% |
| 132–134 | 0 | block | `have h_equation_39_x₁ : P_i.eval x₁.val = P₀.eval y.val + x₁.val * P₁…` | 38 | 2.0% |
| 135–135 | 0 | block | `set f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) => P…` | 27 | 1.4% |
| 136–136 | 0 | block | `set f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := by omega) (f := f…` | 30 | 1.6% |
| 138–140 | 0 | block | `have h_fold_def : f_i_plus_1 y =` | 37 | 1.9% |
| 142–184 | 0 | block | `calc f_i_plus_1 y` | 538 | 28.2% |

반복 논증 후보 (이름을 정규화한 토큰열 유사도 ≥ 0.9, 후보일 뿐 동일성 증명 아님):

- src 115–119 `set P₀_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>…` (124) ↔ src 120–124 `set P₁_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>…` (126), 유사도 0.992
- src 48–54 `have h_eval_qMap_x₀ : (AdditiveNTT.qMap 𝔽q β ⟨i, …` (82) ↔ src 56–62 `have h_eval_qMap_x₁ : (AdditiveNTT.qMap 𝔽q β ⟨i, …` (82), 유사도 0.988
- src 79–85 `have h_cast_0 :` (77) ↔ src 86–93 `have h_cast_1 :` (79), 유사도 0.962
- src 174–175 `apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a …` (46) ↔ src 178–179 `apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a …` (46), 유사도 0.978

## 12. `interleaved_affine_gaps_imply_tensor_gaps` (arklib, 1,353 토큰, OK, 중간 명제형)

감싸는 블록 안으로 내려가서 나눔: `| succ ϑ_sub_1 ih =>` → `| succ ϑ_sub_2 =>`

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 9–9 | 0 | block | `classical` | 1 | 0.1% |
| 10–10 | 0 | block | `intro ϑ` | 2 | 0.1% |
| 11–11 | 0 | block | `induction ϑ with` | 3 | 0.2% |
| 12–14 | 0 | block | `&#124; zero =>` | 6 | 0.4% |
| 15–15 | 0 | wrapper | `&#124; succ ϑ_sub_1 ih =>` | 5 | 0.4% |
| 16–16 | 1 | block | `cases ϑ_sub_1 with` | 3 | 0.2% |
| 17–36 | 1 | block | `&#124; zero =>` | 144 | 10.6% |
| 37–37 | 1 | wrapper | `&#124; succ ϑ_sub_2 =>` | 4 | 0.3% |
| 38–38 | 2 | block | `intro hϑ_gt_0 u hP_multilinearCombine_close_gt` | 4 | 0.3% |
| 41–41 | 2 | block | `let ϑ := ϑ_sub_2 + 1 + 1` | 8 | 0.6% |
| 42–42 | 2 | block | `have hϑ : ϑ = ϑ_sub_2 + 1 + 1 := by rfl` | 13 | 1.0% |
| 44–45 | 2 | block | `set U₀ : Fin (2 ^ (ϑ_sub_2 + 1)) → Word A ι :=` | 30 | 2.2% |
| 46–47 | 2 | block | `set U₁ : Fin (2 ^ (ϑ_sub_2 + 1)) → Word A ι :=` | 30 | 2.2% |
| 48–48 | 2 | block | `unfold jointProximityNat` | 2 | 0.1% |
| 49–49 | 2 | block | `simp only` | 2 | 0.1% |
| 51–63 | 2 | block | `have h_finsnoc_eq_r: ∀ r: Fin (ϑ_sub_2 + 1 + 1) → F,` | 151 | 11.2% |
| 64–65 | 2 | block | `let P : F → (Fin (ϑ_sub_2 + 1) → F) → Prop := fun r_last r_init =>` | 42 | 3.1% |
| 66–67 | 2 | block | `let hP_split_r_last := prob_split_last_uniform_sampling_of_finFun` | 21 | 1.6% |
| 68–68 | 2 | block | `unfold P at hP_split_r_last` | 4 | 0.3% |
| 69–69 | 2 | block | `simp_rw [h_finsnoc_eq_r] at hP_split_r_last` | 6 | 0.4% |
| 70–70 | 2 | block | `rw [hP_split_r_last] at hP_multilinearCombine_close_gt` | 6 | 0.4% |
| 93–93 | 2 | block | `let ϑ_pred := ϑ_sub_2 + 1` | 6 | 0.4% |
| 94–94 | 2 | block | `have h_ϑ_pred : ϑ_pred = ϑ_sub_2 + 1 := by rfl` | 11 | 0.8% |
| 95–95 | 2 | block | `have h_ϑ : ϑ = ϑ_pred + 1 := by rfl` | 11 | 0.8% |
| 99–104 | 2 | block | `have multilinearCombine_snoc_eq_multilinearCombine_affine` | 46 | 3.4% |
| 106–107 | 2 | block | `simp_rw [multilinearCombine_snoc_eq_multilinearCombine_affine]` | 6 | 0.4% |
| 112–112 | 2 | block | `let R_star_set := R_star_tensor MC (m:=ϑ_pred) (e:=e) (ε:=ε) U₀ U₁` | 22 | 1.6% |
| 114–118 | 2 | block | `have h_prob_Rstar_gt_eps_div_q : Pr_{ let r ← $ᵖ F }[ r ∈ R_star_set ]` | 69 | 5.1% |
| 120–132 | 2 | block | `have h_R_star_card_gt_eps : R_star_set.card > ε := by` | 116 | 8.6% |
| 134–139 | 2 | block | `have h_line_close_to_C_m : ∀ (r : R_star_set),` | 53 | 3.9% |
| 141–141 | 2 | block | `have h_C_m_gap := h_interleaved_gaps (2^(ϑ_sub_2 + 1)) (Nat.one_le_tw…` | 16 | 1.2% |
| 143–167 | 2 | block | `have h_prob_line_gt_eps_div_q :` | 354 | 26.2% |
| 169–175 | 2 | block | `have h_final_gap : jointProximityNat₂` | 141 | 10.4% |
| 176–176 | 2 | block | `apply CA_split_rowwise_implies_CA (u := u) (e := e)` | 12 | 0.9% |
| 177–177 | 2 | block | `exact h_final_gap` | 2 | 0.1% |

반복 논증 후보 (이름을 정규화한 토큰열 유사도 ≥ 0.9, 후보일 뿐 동일성 증명 아님):

- src 145–147 `Δ₀(affineLineEvaluation (u₀ := ⋈&#124;(show WordStack …` (83) ↔ src 152–155 `Δ₀(affineLineEvaluation` (85), 유사도 0.988

## 13. `putnam_1964_a4` (putnambench, 1,769 토큰, OK, 중간 명제형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 6–61 | 0 | block | `have h_main : ∃ (i j : ℕ), i < j ∧ (u i = u j ∧ u (i + 1) = u (j + 1)…` | 527 | 29.8% |
| 63–184 | 0 | block | `have h_periodic : ∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n := by` | 1,239 | 70.0% |
| 186–186 | 0 | block | `exact h_periodic` | 2 | 0.1% |

src 63–184 블록(70.0%)을 한 단계 더 나눔:

| src 줄 | 종류 | 첫 줄 | 토큰 | 비중 |
| --- | --- | --- | ---: | ---: |
| 64–64 | have | `obtain ⟨i, j, hij, h_eq⟩ := h_main` | 12 | 0.7% |
| 65–163 | have | `have h₁ : ∀ m : ℕ, u (i + m) = u (j + m) := by` | 1,027 | 58.1% |
| 164–183 | have | `have h₂ : ∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n := by` | 169 | 9.6% |
| 184–184 | other | `exact h₂` | 2 | 0.1% |

반복 논증 후보 (이름을 정규화한 토큰열 유사도 ≥ 0.9, 후보일 뿐 동일성 증명 아님):

- src 98–105 `have h₄ : u (i + (m + 4)) = ((u (i + (m + 4) - 1)…` (167) ↔ src 106–116 `have h₅ : u (j + (m + 4)) = ((u (j + (m + 4) - 1)…` (178), 유사도 0.945
- src 133–136 `have h₁₄ : u (i + (m + 3)) = u (j + (m + 3)) := by` (48) ↔ src 137–140 `have h₁₅ : u (i + (m + 2)) = u (j + (m + 2)) := by` (48), 유사도 0.938
- src 133–136 `have h₁₄ : u (i + (m + 3)) = u (j + (m + 3)) := by` (48) ↔ src 141–144 `have h₁₆ : u (i + (m + 1)) = u (j + (m + 1)) := by` (48), 유사도 0.938
- src 137–140 `have h₁₅ : u (i + (m + 2)) = u (j + (m + 2)) := by` (48) ↔ src 141–144 `have h₁₆ : u (i + (m + 1)) = u (j + (m + 1)) := by` (48), 유사도 0.938

비슷한 case 본문 후보 (본문 토큰 ≥ 8, 유사도 ≥ 0.85):

- src 45 `&#124; inl h₈ =>` (8) ↔ src 48 `&#124; inr h₈ =>` (8), 유사도 1.0
- src 76 `&#124; 1 =>` (19) ↔ src 82 `&#124; 2 =>` (19), 유사도 0.947
- src 76 `&#124; 1 =>` (19) ↔ src 88 `&#124; 3 =>` (19), 유사도 0.947
- src 82 `&#124; 2 =>` (19) ↔ src 88 `&#124; 3 =>` (19), 유사도 0.947

## 14. `putnam_1964_b2` (putnambench, 1,754 토큰, OK, 중간 명제형)

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 7–12 | 0 | block | `have h_no_empty : ∀ (T : Set S), T ∈ P → T.Nonempty := by` | 58 | 3.3% |
| 14–126 | 0 | block | `have h_subset_or_compl : ∀ (A : Set S), A ∈ P ∨ Aᶜ ∈ P := by` | 746 | 42.5% |
| 128–138 | 0 | block | `have h_not_both : ∀ (A : Set S), A ∈ P → Aᶜ ∉ P := by` | 72 | 4.1% |
| 140–292 | 0 | block | `have h_card : P.card = 2 ^ (Fintype.card S - 1) := by` | 875 | 49.9% |
| 294–294 | 0 | block | `exact h_card` | 2 | 0.1% |

src 14–126 블록(42.5%)을 한 단계 더 나눔:

| src 줄 | 종류 | 첫 줄 | 토큰 | 비중 |
| --- | --- | --- | ---: | ---: |
| 15–15 | other | `intro A` | 2 | 0.1% |
| 16–16 | other | `by_contra! h` | 3 | 0.2% |
| 17–17 | have | `have h₁ : A ∉ P := h.1` | 8 | 0.5% |
| 18–18 | have | `have h₂ : Aᶜ ∉ P := h.2` | 8 | 0.5% |
| 20–55 | have | `have h₃ : ∃ (U : Set S), U ∈ P ∧ A ∩ U = ∅ := by` | 256 | 14.6% |
| 57–92 | have | `have h₄ : ∃ (V : Set S), V ∈ P ∧ Aᶜ ∩ V = ∅ := by` | 256 | 14.6% |
| 94–94 | have | `obtain ⟨U, hU, hU'⟩ := h₃` | 10 | 0.6% |
| 95–95 | have | `obtain ⟨V, hV, hV'⟩ := h₄` | 10 | 0.6% |
| 97–104 | have | `have h₅ : U ⊆ Aᶜ := by` | 48 | 2.7% |
| 105–112 | have | `have h₆ : V ⊆ A := by` | 48 | 2.7% |
| 114–122 | have | `have h₇ : U ∩ V = ∅ := by` | 57 | 3.2% |
| 124–124 | have | `have h₈ : U ∩ V ≠ ∅ := hPP U hU V hV` | 14 | 0.8% |
| 125–125 | other | `simp_all [Set.ext_iff]` | 4 | 0.2% |
| 126–126 | other | `<;> aesop` | 2 | 0.1% |

src 140–292 블록(49.9%)을 한 단계 더 나눔:

| src 줄 | 종류 | 첫 줄 | 토큰 | 비중 |
| --- | --- | --- | ---: | ---: |
| 141–141 | other | `classical` | 1 | 0.1% |
| 143–143 | have | `let Q : Finset (Set S) := (Finset.univ : Finset (Set S)) \ P` | 20 | 1.1% |
| 145–211 | have | `have h₁ : P.card = Q.card := by` | 313 | 17.8% |
| 213–258 | have | `have h₂ : P.card + Q.card = 2 ^ Fintype.card S := by` | 242 | 13.8% |
| 260–263 | have | `have h₃ : P.card * 2 = 2 ^ Fintype.card S := by` | 35 | 2.0% |
| 265–270 | have | `have h₄ : Fintype.card S ≥ 1 := by` | 33 | 1.9% |
| 271–291 | have | `have h₅ : P.card = 2 ^ (Fintype.card S - 1) := by` | 214 | 12.2% |
| 292–292 | other | `exact h₅` | 2 | 0.1% |

반복 논증 후보 (이름을 정규화한 토큰열 유사도 ≥ 0.9, 후보일 뿐 동일성 증명 아님):

- src 21–40 `have h₄ : ¬(A ∉ P ∧ ∀ (U : Set S), U ∈ P → A ∩ U …` (139) ↔ src 58–77 `have h₅ : ¬(Aᶜ ∉ P ∧ ∀ (U : Set S), U ∈ P → Aᶜ ∩ …` (139), 유사도 0.986
- src 42–53 `· have h₆ : ¬(∀ (U : Set S), U ∈ P → A ∩ U ≠ ∅) :…` (86) ↔ src 79–90 `· have h₇ : ¬(∀ (U : Set S), U ∈ P → Aᶜ ∩ U ≠ ∅) …` (86), 유사도 0.93
- src 97–104 `have h₅ : U ⊆ Aᶜ := by` (48) ↔ src 105–112 `have h₆ : V ⊆ A := by` (48), 유사도 1.0

## 15. `putnam_1995_a3` (putnambench, 4,085 토큰, OK, 중간 명제형)

감싸는 블록 안으로 내려가서 나눔: `have h_main : ∀ (d e f : (Fin 9 → ℤ)), …`

| src 줄 | 깊이 | 역할 | 첫 줄 | 토큰 | 비중 |
| --- | ---: | --- | --- | ---: | ---: |
| 7–7 | 0 | wrapper | `have h_main : ∀ (d e f : (Fin 9 → ℤ)), ((relation d e) ∧ (relation e …` | 48 | 1.2% |
| 8–8 | 1 | block | `intro d e f h` | 5 | 0.1% |
| 9–9 | 1 | block | `have h₁ : relation d e := h.1` | 8 | 0.2% |
| 10–10 | 1 | block | `have h₂ : relation e f := h.2` | 8 | 0.2% |
| 11–13 | 1 | block | `have h₃ : ∀ (i : Fin 9), 7 ∣ (digits_to_num (fun j : Fin 9 => if j = …` | 83 | 2.0% |
| 14–16 | 1 | block | `have h₄ : ∀ (i : Fin 9), 7 ∣ (digits_to_num (fun j : Fin 9 => if j = …` | 83 | 2.0% |
| 18–65 | 1 | block | `have h₅ : ∀ (i : Fin 9), 7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digit…` | 812 | 19.9% |
| 67–114 | 1 | block | `have h₆ : ∀ (i : Fin 9), 7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digit…` | 812 | 19.9% |
| 116–189 | 1 | block | `have h₇ : 7 ∣ digits_to_num e + digits_to_num d := by` | 1,160 | 28.4% |
| 191–222 | 1 | block | `have h₈ : ∀ (i : Fin 9), 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by` | 521 | 12.8% |
| 224–277 | 1 | block | `have h₉ : ∀ (i : Fin 9), 7 ∣ d i - f i := by` | 525 | 12.9% |
| 279–279 | 1 | block | `intro i` | 2 | 0.0% |
| 280–280 | 1 | block | `have h₁₀ : 7 ∣ d i - f i := h₉ i` | 13 | 0.3% |
| 281–281 | 1 | block | `exact h₁₀` | 2 | 0.0% |
| 282–282 | 0 | block | `exact h_main` | 2 | 0.0% |

반복 논증 후보 (이름을 정규화한 토큰열 유사도 ≥ 0.9, 후보일 뿐 동일성 증명 아님):

- src 18–65 `have h₅ : ∀ (i : Fin 9), 7 ∣ (e i - d i) * (10 : …` (812) ↔ src 67–114 `have h₆ : ∀ (i : Fin 9), 7 ∣ (f i - e i) * (10 : …` (812), 유사도 1.0
- src 11–13 `have h₃ : ∀ (i : Fin 9), 7 ∣ (digits_to_num (fun …` (83) ↔ src 14–16 `have h₄ : ∀ (i : Fin 9), 7 ∣ (digits_to_num (fun …` (83), 유사도 1.0
