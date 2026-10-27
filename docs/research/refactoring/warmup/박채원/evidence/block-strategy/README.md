# 웜업 블록 전략: 규칙 기반 블록 분할과 조합 선택

증명을 블록 트리로 나누고, 컴파일로 확인한 변경 후보 중 서로 겹치지 않으면서 proof token 감소가 가장 큰 조합을 고름. LLM은 쓰지 않으며 같은 입력이면 항상 같은 결과가 나옴. 처음에는 중간 명제형(`have`로 중간 사실을 세워 가며 결론에 이르는 증명, 4·10–15번)을 대상으로 만들었고, 분기형용 규칙 8을 더해 웜업 15문제 전체에 적용함.

수치는 지정 버전에서 측정한 로컬 측정값임. 토큰은 공식 `proof_length` 규칙으로 세지만 공식 Arena 평가 결과는 아님.

## 규칙

1. 스택: 들여쓰기로 블록 트리를 만듦. 블록 하나 = 한 줄 + 그 아래 하위 증명.
2. DFS: 블록별 토큰 합을 구하고, 루트 합 + `:= by` 줄 토큰이 공식 `proof_length`와 같은지 확인함.
3. 해시: 지역 이름을 v0, v1, …로 바꿔 해시가 같은 블록(이름만 다른 중복)을 묶음.
4. 편집 거리 DP: 거의 같은 `have` 블록 쌍과 서로 다른 토큰(함수 인자 후보)을 기록함. 보고만 함.
5. 우선순위 큐: 예상 감소량이 큰 중복 그룹부터 묶어 컴파일해 봄.
6. 메모이제이션: 같은 파일 내용은 다시 컴파일하지 않음(`cache.json`).
7. 트리 DP: 서로 겹치지 않는 후보 조합 중 감소량이 가장 큰 것을 고르고, 한꺼번에 적용해 다시 컴파일함.
8. 분기 합치기: 본문이 글자까지 같은 분기(`case a =>`, `case b =>`)를 `case a | b =>` 하나로 합침. `| p =>` 형태의 분기도 같은 방식(`| p | q =>`)으로 합침.

후보는 세 종류임.

- 미사용 블록 제거: `linter.unusedVariables.analyzeTactics`가 경고한 `have` 블록을 지우고 컴파일하는 과정을 경고가 없을 때까지 반복함([prune_unused.py](prune_unused.py)).
- 중복 블록을 보조정리로 묶기: 첫 멤버 자리에 `have blk_genK : ∀ (인자), 명제 := by …`를 두고 각 멤버를 `blk_genK 인자`로 바꿈. 예를 들어 15번의 `h₅`(d, e)와 `h₆`(e, f)를 `blk_gen1` 하나로 묶으면 748토큰이 줄어듦.
- 같은 본문의 분기 합치기(규칙 8): 예를 들어 1번의 `case fvar`와 `case op`를 `case fvar | op =>` 하나로 합치면 18토큰이 줄어듦.

구현은 규칙 1–4가 [block_tree.py](block_tree.py), 5–8이 [block_dp.py](block_dp.py)임.

## 결과 (웜업 15문제)

웜업 15문제는 다섯 저장소에서 세 문제씩 가져온 구성임(1–3번 Strata, 4–6번 PhysLib, 7–9번 CSLib, 10–12번 ArkLib, 13–15번 PutnamBench).

| # | 출처 | 정리 | 시작 | 미사용 블록 제거만 | 규칙 1–8 최종 | 감소율 |
| ---: | --- | --- | ---: | ---: | ---: | ---: |
| 1 | Strata | `CallElimCorrect.substOldPostSubset` | 313 | 298 | 280 | 10.54% |
| 2 | Strata | `CallElimCorrect.extractedOldExprInVars` | 222 | 222 | 222 | 0.00% |
| 3 | Strata | `Core.InitsUpdatesComm` | 224 | 224 | 224 | 0.00% |
| 4 | PhysLib | `fundamental_theorem_of_variational_calculus'` | 851 | 851 | 851 | 0.00% |
| 5 | PhysLib | `…time_deriv_time_deriv_electricField_of_isExtrema` | 1,372 | 1,372 | 1,372 | 0.00% |
| 6 | PhysLib | `…ι_timeOrderF_superCommuteF_eq_time` | 1,217 | 1,217 | 1,217 | 0.00% |
| 7 | CSLib | `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress` | 408 | 408 | 408 | 0.00% |
| 8 | CSLib | `Cslib.SKI.parallelReduction_diamond` | 407 | 407 | 407 | 0.00% |
| 9 | CSLib | `Cslib.CCS.bisimilarity_congr_choice` | 251 | 251 | 251 | 0.00% |
| 10 | ArkLib | `…fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius` | 1,463 | 1,463 | 1,463 | 0.00% |
| 11 | ArkLib | `…fold_advances_evaluation_poly` | 1,906 | 1,906 | 1,906 | 0.00% |
| 12 | ArkLib | `interleaved_affine_gaps_imply_tensor_gaps` | 1,353 | 1,353 | 1,353 | 0.00% |
| 13 | PutnamBench | `putnam_1964_a4` | 1,769 | 1,749 | 1,721 | 2.71% |
| 14 | PutnamBench | `putnam_1964_b2` | 1,754 | 1,534 | 1,534 | 12.54% |
| 15 | PutnamBench | `putnam_1995_a3` | 4,085 | 3,918 | 3,130 | 23.38% |

- 시작 토큰은 15문제 모두 공식 `proof_length`와 같음.
- 15문제 모두 원본과 최종 증명이 컴파일되고, 최종 증명의 공리는 원본과 같음(`propext`, `Classical.choice`, `Quot.sound` 또는 그 일부).
- 줄어든 4문제(1, 13–15번)는 트리 DP의 예측 감소량과 다시 센 감소량이 같음(33, 48, 220, 955).
- 최종 증명은 `results/dpK/final.lean`에 있음. 후보별 컴파일 결과는 `cache.json`, 고른 조합은 `result.json`에 있음.

### 라이브러리 증명에서 거의 줄지 않은 이유

- 미사용 `have`: 린터 옵션을 켠 컴파일에서 "unused variable" 경고가 라이브러리 12문제 중 1번에서만 1건(`have assoc`) 나옴. 같은 컴파일에서 다른 경고는 나오므로 린터는 동작함. 라이브러리 증명은 스타일 검사를 거쳐 쓰지 않는 `have`가 거의 없음.
- 중복 블록: 라이브러리 12문제 중 중복 블록이 있는 문제는 1, 6, 10, 11, 12번뿐임. 1번은 규칙 8로 합침. 10, 11번과 6번 일부는 `have 이름 : 명제 := by` 한 줄 형식이 아니고, 12번과 6번 일부는 tactic 블록 밖(항 자리)에 있어 `trace_state`로 문맥을 읽을 수 없음.
- 사람이 쓴 PutnamBench 풀이에서는 효과가 크고, 이미 다듬어진 라이브러리 증명에서는 이 규칙들로 줄일 부분이 거의 없었음.

### 묶지 못한 중복 (13–15번)

14번 그룹 1–4는 다른 부분이 `A`/`Aᶜ` 같은 식이라 인자로 바꿀 수 없음. 14번 그룹 5와 15번 그룹 2·3은 `have 이름 : 명제 := by` 한 줄 형식이 아님.

## 신뢰구간

"이 규칙을 비슷한 문제에 적용하면 토큰이 평균 몇 % 줄어들까"를 측정한 문제들로 추정한 범위임([reduction_ci.py](reduction_ci.py)). 문제 하나의 감소율을 표본 하나로 봄. 같은 문제는 다시 재도 값이 같으므로(컴파일과 토큰 수가 결정적), 범위의 폭은 문제마다 감소율이 다른 정도에서만 나옴.

| 대상 | 측정한 문제 수 | 평균 감소율 | 95% 신뢰구간 (t 분포) | 95% 신뢰구간 (부트스트랩) |
| --- | ---: | ---: | --- | --- |
| 웜업 전체 | 15개 | 3.28% | −0.53%–7.08% | 0.36%–7.05% |
| 라이브러리 (Strata·PhysLib·CSLib·ArkLib) | 12개 | 0.88% | | |
| PutnamBench | 3개 | 12.88% | | |

- 출처에 따라 결과가 크게 갈림. 15문제 전체 평균은 두 그룹을 섞은 값이라 평균 하나로 요약하기 어려움.
- t 분포 구간의 하한이 0보다 작은 것은 감소율 대부분이 0이고 표본이 적기 때문임(이 규칙은 토큰을 늘리지 않음). 그룹별 구간은 문제 수가 적어 따로 내지 않음.

## 환경과 한계

- 13–15번: Lean v4.26.0, Mathlib v4.26.0(커밋 `2df2f01`, [project/](project/)로 고정), 대회 데이터 header, `lake env lean`.
- 나머지 12문제: 저장소 원본 파일의 해당 줄만 바꿔 `lake lean`으로 컴파일하는 파일 모드. 실행 후 원본 파일은 바이트 단위로 복구됨. 데이터의 줄 번호가 파일과 맞지 않는 문제(1–3, 8번)는 증명 원문으로 위치를 찾음.
  - Strata 커밋 `451e5f0`(v4.26.0): 1–3번. 3번은 데이터에 v4.29.1·v4.27.0·v4.26.0이 함께 적혀 있으며 그중 v4.26.0으로 측정함.
  - PhysLib 커밋 `c484336`(v4.32.0): 4–6번.
  - CSLib 커밋 `197a7be`(v4.32.0): 7–9번. 데이터에 적힌 버전 중 PhysLib과 같은 Mathlib 커밋을 쓰는 버전을 고름.
  - ArkLib 커밋 `c1712f6`(v4.31.0): 10–12번.
- 린터가 일부 미사용 변수를 놓칠 수 있어(false negatives) 미사용 블록 제거 결과는 하한임.
- 보조정리로 묶기는 이름만 다른 블록, `have 이름 : 명제 := by` 한 줄 형식, tactic 블록 안의 멤버만 다룸. 분기 합치기는 본문이 글자까지 같은 분기만 다룸.
- heartbeat는 재지 않음.

## 실행

```powershell
Set-ExecutionPolicy -Scope Process Bypass -Force
.\run_13_15.ps1 -Jsonl <benchmark_data_warmup.jsonl>
```

나머지 12문제(파일 모드)는 해당 저장소를 지정 커밋으로 받아 빌드한 뒤 실행함.

```bash
python prune_unused.py --jsonl <jsonl> --row 1 --repo <Strata> --out results/prune1
python block_dp.py --jsonl <jsonl> --row 1 --repo <Strata> --prune results/prune1 --out results/dp1
python reduction_ci.py results/dp*/result.json --md results/ci.md --json results/ci.json
```

## 지난주에 이어 이번 주에 새롭게 추가한 아이디어

지난주에는 14, 15번 증명을 블록으로 나누고 블록 조합별 토큰을 잼. 이번 주에는 블록을 나누고 고르는 방법을 규칙으로 정해 자동화하고, 웜업 15문제 전체에 적용함.

- 중복된 블록은 하나로 통합하고, 재귀 함수처럼 블록을 함수 하나로 묶음. 분기형에서는 같은 본문의 분기를 하나로 합침.
- 스택, 해시, 큐 자료구조로 블록을 나누고 찾고 시도 순서를 정함.
- 블록 조합 선택은 DP로 함.
- 자동 단계는 미사용 `have` 반복 제거로 한정하고, 목표는 토큰만 봄(heartbeat 제외).
- 기대 효과는 문제 간 변동 기준 신뢰구간으로 냄.

코드는 Claude와 함께 작성.
