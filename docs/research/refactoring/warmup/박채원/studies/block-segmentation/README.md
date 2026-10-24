# 블록 분할 기준 학습: Lean InfoTree와 Strata·CSLib 증명

- 작성: 박채원, 구조/전략 설계 그룹, 2026-10-20
- 범위: 참조 증명을 어떤 단위로 나눌지 정하기 위해 Lean InfoTree와 Warm-up 1–3, 7–9번(Strata, CSLib) 증명 구조를 정리하고, Warm-up 15문제를 유형별로 묶어 분할 규칙을 정함.
- 근거: [블록 분석기 결과](../../evidence/block-analyzer/README.md), [웜업 블록 전략](../../evidence/block-strategy/README.md)

## 1. 블록으로 나누는 이유와 한계

- 대회 proof token(`proof_length`)은 줄마다 센 값을 더한다. 블록을 바꾸면 그 블록의 토큰만 변하므로 블록별 기여를 정확히 나눌 수 있다. 15번 블록 조합 32개에서 블록별 감소의 합이 전체 감소와 일치했다([블록 조합 실험](../../evidence/block-combinations-15/README.md)).
- 블록 안의 증명만 바꾸면 블록 경계를 넘는 감소는 얻지 못한다. 15번은 다섯 블록의 증명만 바꾸면 443토큰이고, 중간 명제 자체를 바꾼 수정한 증명은 283토큰이다.

## 2. 분할 기준

| 기준 | 방식 | 맞는 증명 | 한계 |
| --- | --- | --- | --- |
| 고정 줄 수 | 5·10·20줄 단위. Lean Refactor 논문 3.3절, 부록 I.4 | 형태와 무관하게 적용 | 논리 단위와 어긋남 |
| 들여쓰기 블록 | 최상위 tactic과 그 아래 들여쓴 줄 | 텍스트만으로 적용. 현재 블록 분석기의 기준 | `calc` 단계나 여러 줄 식도 블록이 됨 |
| `have` 블록 | 중간 명제와 그 증명 | Putnam, PhysLib, ArkLib | `have`가 적은 귀납 증명에는 덜 맞음 |
| `case` 블록 | 귀납·경우 분석의 분기 하나 | Strata, CSLib | 분기 안의 반복은 별도 비교가 필요 |
| 의존성 기반 | InfoTree로 목표 변화와 변수 사용을 추적 | 모든 증명 | 문제의 Lean 환경에서 실행해야 함 |

## 3. Lean InfoTree

### 3.1 정의

Lean v4.26.0 `src/lean/Lean/Elab/InfoTree/Types.lean` 259–287줄:

> "The InfoTree is a structure that is generated during elaboration and used by the language server to look up information about objects at particular points in the Lean document."

- 노드는 `context`, `node`, `hole` 세 종류다. `node`의 자식은 "information for nested term elaboration and tactic evaluation"이다.
- tactic 노드의 정보 `TacticInfo`(같은 파일 134–144줄)는 tactic 실행 전후의 목표 `goalsBefore`, `goalsAfter`를 저장한다. VS Code Infoview에 보이는 목표가 이 정보다.
- 따라서 InfoTree를 읽으면 tactic마다 어떤 목표를 받아 어떤 목표를 남겼는지, 어떤 지역 변수가 쓰였는지를 증명 구조 그대로 얻을 수 있다.

### 3.2 InfoTree를 쓰는 공식 도구: 사용되지 않는 변수 린터

`src/lean/Lean/Linter/UnusedVariables.lean` 17–18줄: "This file implements the unused variable linter, which runs automatically on all commands and reports any local variables that are never referred to, using information from the info tree."

- 기본값으로는 tactic 증명 안의 지역 변수를 검사하지 않는다(같은 파일 38줄).
- `set_option linter.unusedVariables.analyzeTactics true`를 켜면 tactic 증명 안의 지역 변수까지 검사한다(99–107줄). 설명문은 이 경우 일부를 놓칠 수 있다(false negatives)고 적는다.

### 3.3 13–15번 참조 증명에 적용

Lean v4.26.0, 대회 데이터의 header(`import Mathlib`) 그대로 위 옵션을 켜고, 보고된 `have` 블록을 지운 뒤 다시 컴파일하는 과정을 보고가 없을 때까지 반복했다([블록 전략](../../evidence/block-strategy/README.md)).

| 문제 | 반복 횟수 | 지운 블록 | proof token |
| --- | ---: | ---: | --- |
| 13번 | 1 | 2 | 1,769 → 1,749 |
| 14번 | 2 | 13, `h_no_empty` 포함 | 1,754 → 1,534 |
| 15번 | 1 | 7 | 4,085 → 3,918 |

- 모든 단계가 에러 없이 컴파일되고 공리는 표준 3개다.
- 14번 `h_no_empty`는 structure-design.md에서 손으로 찾은 "뒤에서 쓰이지 않는 사실"과 같다.
- 지운 뒤 다시 컴파일하면 새로 쓰이지 않게 된 `have`가 나온다(14번 2회차). 그래서 반복이 필요하다.
- 토큰은 공식 `proof_length` 재구현으로 셌다. 지정 버전(v4.26.0)과 대회 헤더로 컴파일한 로컬 측정값이며, 공식 Arena 평가 결과는 아니다.

### 3.4 분할 기준에 주는 의미

- 블록 안을 고치기 전에 쓰이지 않는 `have` 블록을 먼저 지우는 단계를 둘 수 있다. 이 단계는 LLM 없이 Lean만으로 실행된다.
- 블록 사이의 의존 관계, 즉 어떤 블록의 명제를 뒤에서 몇 번 쓰는지도 InfoTree에서 얻을 수 있다. 이번에는 린터 출력만 사용했고 InfoTree를 직접 읽는 코드는 만들지 않았다.

## 4. Strata·CSLib 증명 구조

### 4.1 공통 패턴

Warm-up 1–3번(Strata), 7–9번(CSLib)은 `induction` 또는 `cases` 뒤에 생성자마다 `case tag =>` 분기를 둔다. 8번은 분기 안에서 다시 `cases`로 나눈다.

| 문제 | 공식 토큰 | 최상위 `case` 블록 수 | `case` 블록 토큰 비중 | 가장 큰 블록 |
| --- | ---: | ---: | ---: | --- |
| 1 | 313 | 9 | 97.4% | `case app` 22.7% |
| 2 | 222 | 5 | 91.4% | `case app` 34.7% |
| 3 | 224 | 2 | 83.9% | `case update_some` 73.7% |
| 7 | 408 | 10 | 94.1% | `case app` 19.4% |
| 8 | 407 | 5 | 97.8% | `case par` 39.3% |
| 9 | 251 | 2 | 92.0% | `case right` 46.2% |

이 증명들은 `have` 블록이 거의 없고 토큰 대부분이 `case` 분기 안에 있다. 이 출처에서는 `case` 분기 하나가 자연스러운 블록 단위다.

### 4.2 비슷한 분기 본문

블록 분석기가 분기 본문(본문 토큰 8 이상)을 변수명 정규화 후 비교한 결과다. 유사도 0.85 이상만 적었다.

| 문제 | 분기 쌍 | 본문 토큰 | 유사도 |
| --- | --- | --- | ---: |
| 1 | `case fvar` ↔ `case op` | 17, 17 | 1.0 |
| 1 | `case const` ↔ `case bvar` | 10, 10 | 1.0 |
| 7 | `case inl` ↔ `case inr` | 29, 29 | 0.966 |
| 7 | `case abs` ↔ `case tabs` | 22, 22 | 0.955 |
| 8 | `case red_I` ↔ `case red_K` (안쪽 분기) | 11, 11 | 1.0 |
| 9 | `case left` ↔ `case right` | 112, 113 | 0.978 |

- 분기 본문은 대부분 수십 토큰이라 `have` 블록 기준(40토큰 이상)의 반복 탐지에는 걸리지 않는다. 분기 단위 비교를 따로 둬야 한다.
- Lean v4.26.0 `src/lean/Init/Tactics.lean` 283–290줄은 "`case tag₁ | tag₂ => tac` is equivalent to `(case tag₁ => tac); (case tag₂ => tac)`"라고 정의한다. 본문이 같은 분기는 이 형태로 합칠 수 있는 후보다.
- 1–3, 7–9번은 Strata, CSLib 저장소의 지정 커밋이 필요해서 이번에는 컴파일하지 않았다. 위 표는 후보이고, 합친 증명이 컴파일되는지는 확인하지 않았다.

## 5. Warm-up 유형 분류와 유형별 분할 규칙

블록 분석기는 최상위 블록을 `case` 분기, `calc` 단계, `have` 계열(`have`, `obtain`, `let`, `set` 등), 기타로 나누고, 토큰 비중이 50% 이상인 종류로 증명 유형을 정한다. 결과는 [blocks.md](../../evidence/block-analyzer/blocks.md)의 "유형별 묶음"에 있다.

| 유형 | 문제 | 출처 | 분할 규칙 |
| --- | --- | --- | --- |
| 분기형 | 1, 2, 3, 7, 8, 9 | Strata, CSLib | `case` 분기 하나가 블록. 큰 분기 안의 분기는 한 단계 더 나누고, 분기 본문끼리 비교한다 |
| 계산 연쇄형 | 5, 6 | PhysLib | `calc` 단계 하나(`_ = …`와 그 근거)가 블록. 큰 `calc`는 단계 단위로 나눈다 |
| 중간 명제형 | 4, 10, 11, 12, 13, 14, 15 | PhysLib, ArkLib, PutnamBench | `have` 하나와 그 증명이 블록. 감싸는 `have`는 안으로 내려가고, 큰 `have`는 안쪽 `have` 단위로 나누며, 사용되지 않는 `have`는 린터로 찾는다 |

| # | case | calc | have | 기타 |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 97.4% | 0% | 0% | 2.2% |
| 2 | 91.4% | 0% | 0% | 8.1% |
| 3 | 83.9% | 0% | 9.4% | 6.2% |
| 4 | 0% | 0% | 95.1% | 4.8% |
| 5 | 0% | 81.2% | 11.5% | 7.1% |
| 6 | 0% | 70.3% | 10.2% | 18.2% |
| 7 | 94.1% | 0% | 2.2% | 3.4% |
| 8 | 97.8% | 0% | 0% | 2.0% |
| 9 | 92.0% | 0% | 0% | 7.6% |
| 10 | 0% | 0% | 93.9% | 6.0% |
| 11 | 0% | 28.2% | 71.1% | 0.6% |
| 12 | 11.1% | 0% | 84.3% | 3.9% |
| 13 | 0% | 0% | 99.8% | 0.1% |
| 14 | 0% | 0% | 99.8% | 0.1% |
| 15 | 0% | 0% | 98.5% | 0.3% |

비중은 반올림 때문에 합이 100%와 조금 다를 수 있다. 블록 하나가 전체의 40% 이상이면 같은 들여쓰기 규칙으로 한 단계 더 나눈다. 이 단계에서 보인 것:

- 14번 `h_subset_or_compl`(42.5%) 안의 `h₃`, `h₄`가 각 256토큰으로 나뉜다. structure-design.md에서 손으로 센 값과 같다.
- 13번 `h_periodic`(70.0%) 안에서 `h₁` 하나가 전체의 58.1%다.
- 6번 `calc`(70.3%)는 다섯 단계로 나뉘고, 세 번째 단계가 전체의 29.7%다.
- 9번 `case left`, `case right` 안은 각각 `case choice`(70토큰), `case bisim`(37·38토큰)으로 같은 구성이다.

유형은 블록 종류의 토큰 비중으로만 정한 것이며, 문제의 수학적 내용이나 난이도를 분류한 것은 아니다.

## 6. 블록 분석기에 반영한 것과 남은 것

- 반영: `case`와 `| tag =>` 분기 본문 비교, 증명 유형 분류, 40% 이상 블록의 한 단계 추가 분할, 미사용 `have` 반복 제거([블록 전략](../../evidence/block-strategy/README.md)).
- 남은 것
  1. InfoTree를 직접 읽어 블록 사이 의존 관계를 얻는 기능.
  2. Strata, CSLib, PhysLib, ArkLib 지정 환경에서의 컴파일과 블록별 heartbeat.

## 출처

- Lean v4.26.0 소스: `Lean/Elab/InfoTree/Types.lean`, `Lean/Linter/UnusedVariables.lean`, `Init/Tactics.lean`.
- Lean Refactor 논문 arXiv:2605.20244 3.3절, 부록 I.4.
- Warm-up 증명: 대회 benchmark JSONL `benchmark_data_warmup.jsonl`의 `src`.
