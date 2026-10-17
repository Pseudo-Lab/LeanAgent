# Lean Refactor 논문: Week 3 구조·전략 설계에 필요한 부분

- 작성: 박채원, 구조/전략 설계 그룹 · Week 3 모임 2026-10-18 공유
- 논문: [Lean Refactor: Multi-Objective Controllable Proof Optimization via Agentic Strategy Search](https://arxiv.org/abs/2605.20244), arXiv:2605.20244
- 정리 범위: Lean Refactor 논문에서 Week 2 때 다루지 않았던 부분을 다룸. Week 3 주제인 기존 증명 분석과 리팩터링 후보를 만드는 전략에 필요한 2장, 부록 B.4·B.5·B.8, C, D, N을 정리함.

## 1. 2장: 리팩터링이 LLM에게 어려운 이유

2장은 세 가지 어려움을 제시함.

### 1.1 증명 최적화는 다목적 문제임

- 원문: "compilation cost is an equally important complexity metric, and the two are not always aligned"
- 원문: "Token length fails to predict compilation cost because of short, heavy tactics"

토큰 수로 컴파일 비용을 예측할 수 없음. `nlinarith`, `simp_all` 같은 한 단어짜리 tactic이 내부에서 큰 탐색을 하기 때문임. 구체적인 예는 부록 D에 있음.

### 1.2 Lean 저장소의 버전 호환은 깨지기 쉬움

- 원문: "weekly releases frequently rename declarations and break imports even across patch versions"
- 원문: "every recent frontier model's training cutoff lands before recent Mathlib releases"

Mathlib은 거의 매주 바뀌고 정리 이름도 자주 바뀜. LLM은 학습 시점 이전의 이름만 알기 때문에 없어진 이름을 쓴 증명을 낼 수 있음.

### 1.3 대회 문제와 연구 수준 증명의 차이

연구 수준 증명은 불러 쓰는 정리가 대회 문제보다 훨씬 많음. Week 3에서 다루는 Warm-up 14·15는 Putnam 문제라 짧게만 적음.

## 2. 부록 B: 전략을 기록하는 방법

3.1절의 전략 정의: "Each entry is a reusable refactoring pattern distilled from a raw long–short proof pair". 부록 B는 전략을 만드는 과정을 8단계로 설명함. 그중 리팩터링 후보를 만드는 전략을 기록하는 데 바로 쓸 수 있는 세 절만 정리함.

| 절 | 내용 |
| --- | --- |
| B.4 | **위치 고정**: 긴 증명과 짧은 증명의 쌍에서 전략을 뽑을 때, 각 전략을 긴 증명의 특정 부분에 연결함. 원문: "ground each extracted strategy to a specific component of the original long proof". 지어낸 전략이 줄고, 검색 모델의 학습 신호가 됨. 증명 전체를 바꾸는 전략은 더 큰 연속 구간에 연결함. |
| B.5 | **전략 형식**: 6개 필드로 적음. Title, Description, When to Apply, Application Guide, Abstract Example, Potential Reduction. Potential Reduction은 high, medium, low 세 등급임. Abstract Example은 정리 고유의 이름을 지워 다른 증명에도 옮겨 쓸 수 있게 함. |
| B.8 | **전략 단위 메타데이터**: 컴파일 시간 감소는 그 전략에 묶인 쌍들의 중앙값임. 버전 호환 집합은 묶인 짧은 증명들이 모두 컴파일되는 툴체인의 교집합임. 그래서 호환성 추정이 보수적임. |

나머지 B.1–B.3, B.6, B.7은 데이터 출처, 쌍 생성, 품질 판정, 중복 제거를 다루는 데이터 과정이라 이번에는 다루지 않음. 원시 추출 481,567개가 고유 전략 9,237개로 줄었다고 보고함.

## 3. 부록 N: 전략 예시

부록 N은 전략 두 개를 B.5의 형식으로 보여 줌.

| 필드 | 전략 1 | 전략 2 |
| --- | --- | --- |
| Title | "Eliminate exhaustive numeric case analysis; construct new witness via arithmetic shift" | "Replace per-entry have lemmas with a single ext and fin_cases proof" |
| When to Apply | 가정이 ∃ x, ∀ y, P x y 꼴이고, 목표는 그 변수를 상수만큼 옮긴 같은 명제이며, 남은 목표가 증인의 구체적인 값에 의존하지 않을 때 | 유한 타입으로 인덱스된 행렬의 등식을 증명하면서, 성분마다 `have`를 따로 썼을 때 |
| 바꾸는 방식 | 가정을 여러 점에 대입해 증인을 숫자로 확정하던 것을, 존재 가정을 풀어 옮긴 증인을 주고 그 점에서 가정을 적용해 끝냄 | 성분별 `have`를 모두 지우고 `ext i j`, `fin_cases i <;> fin_cases j`, `simp` 한 번으로 끝냄 |
| Reduction | large | medium |

전략 2는 같은 꼴의 `have`를 여러 번 쓰던 것을 한 번의 증명으로 바꾸는 전략임. Week 3에서 본 15번 참조 증명의 `h₅`·`h₆` 반복과 같은 종류의 낭비를 다룸.

B.5는 Potential Reduction을 high, medium, low로 정의하지만, 부록 N의 예시는 large, medium으로 적혀 있음.

## 4. 부록 D: 짧은 증명이 더 비쌀 때

miniF2F 문제 `amc12_2001_p21`의 두 증명을 비교함. 변수 a, b, c, d는 자연수이고, a·b·c·d = 8!과 합·곱 조건 세 개가 주어지며, 목표는 a − d = 10임.

| | 짧은 증명 | 긴 증명 |
| --- | --- | --- |
| 방식 | `norm_num [Nat.factorial] at h0` 뒤 `nlinarith`로 b ≤ 525를 얻고, `interval_cases b <;> simp_all <;> nlinarith`로 끝냄. 원문: "relies on a single heavy cascade" | 조건을 (a+1)(b+1) = 525, (b+1)(c+1) = 147, (c+1)(d+1) = 105로 바꿔 b = 20, a = 24, c = 6, d = 14를 차례로 확정하고 `exact_mod_cast`로 끝냄. 원문: "spans over 130 lines" |
| 결과 | 무거운 tactic이 수백 개 경우에서 실행됨 | "compiles more than 20× faster than its shorter counterpart" |

부록 D에는 토큰 수와 절대 컴파일 시간이 나오지 않음.

## 5. 부록 C와 6장: 한계

6장 원문: "Cross-version evaluation is limited to PutnamBench due to toolchain-pinned research projects, and strategy-level metadata uses conservative cluster-level aggregation rather than marginal attribution". 부록 C는 이 두 가지를 자세히 설명함.

1. **버전 간 평가 범위**: 연구 저장소는 특정 Lean·Mathlib 툴체인에 깊이 묶여 있어, 툴체인을 바꾸면 리팩터링 품질과 상관없이 컴파일이 깨짐. 그래서 버전 간 실험은 PutnamBench로만 함.
2. **함께 낸 효과를 나누지 못함**: 원문: "Strategy-level compile-time annotations are computed as the cluster median of pair-level reductions, where each pair contributes the joint speedup of its refactorings". 버전 호환 집합도 교집합이라 전략 하나의 몫을 따로 알 수 없음. 원문: "Disentangling marginal per-strategy contributions, via Shapley-style attribution, or regression over co-occurrence indicators" 는 후속 과제로 남김.

## 6. 구조/전략 설계에 가져갈 점

아래는 위 내용을 바탕으로 한 내 해석임.

1. **후보는 두 축을 모두 재야 함.** 2장과 부록 D를 보면 토큰 감소만으로 heartbeat 감소를 말할 수 없음. 대회 점수가 두 축을 따로 재서 평균하는 것과 맞음.
2. **변경은 증명의 위치와 함께 기록함.** 논문은 전략을 긴 증명의 특정 부분에 묶음. 내 [14·15 블록별 비교](../../refactoring/warmup/박채원/structure-design.md)도 참조 증명의 줄 범위와 수정한 증명의 줄 범위를 짝지었음.
3. **변경을 B.5의 6필드로 적으면 공유하기 쉬움.** 15번 참조 증명의 `h₅`·`h₆`는 변수만 다른 같은 논증이고 각 812 토큰임. 이것을 보조정리 하나로 바꾼 변경은 다음처럼 적을 수 있음.

| 필드 | 내용 |
| --- | --- |
| Title | 변수만 다른 두 블록을 일반화 보조정리 하나로 |
| Description | 두 블록이 인자만 다르면, 인자를 받는 보조정리를 한 번 증명하고 두 번 씀 |
| When to Apply | 지역 이름을 바꾸면 같아지는 블록이 두 개 이상 있을 때 |
| Application Guide | 공통 명제를 `∀ x y …`로 일반화해 증명하고, `simp only [key] at …`로 적용함 |
| Abstract Example | 참조 27–123줄, 1,624토큰 → 수정한 증명 21–27줄, 135토큰 |
| Potential Reduction | high |

4. **효과를 나누려면 한 번에 하나씩 바꿔 재야 함.** 논문도 전략별 기여를 분리하지 못한 것을 한계로 적었음. 내 블록 비교도 같은 이유로 블록별 heartbeat 기여를 말하지 못함. 참조 증명에서 한 블록만 바꾼 파일을 따로 재는 것이 이 문제를 직접 다루는 방법임.
5. **호환성은 지정 버전 전부에서 확인함.** 논문은 전략의 호환 집합을 교집합으로 잡음. 대회도 지정 버전 중 그대로 컴파일되는 비율인 zero-shot %를 점수에 넣음.

## 출처

- 논문: arXiv:2605.20244, https://arxiv.org/pdf/2605.20244, 2026-10-17 확인. 인용은 2장, 3.1절, 6장, 부록 B·C·D·N의 원문임.
- 15번 토큰 수: [structure-design.md](../../refactoring/warmup/박채원/structure-design.md), 공식 `proof_length` 재구현으로 계산함.
