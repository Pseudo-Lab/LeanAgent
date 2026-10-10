# LeanDojo: Lean 기본 개념으로 읽는 정리 증명 환경

- 분야: `Lean&Mathlib` (`Automated Theorem Proving`, `Verifier-guided Agent` 태그도 있음)
- 논문: Kaiyu Yang et al., [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](https://arxiv.org/abs/2306.15626v2), NeurIPS 2023 Datasets and Benchmarks Track
- 코드: [LeanDojo](https://github.com/lean-dojo/LeanDojo), [ReProver](https://github.com/lean-dojo/ReProver) (MIT License)
- 정리 범위: 본문 1~7장 (부록 제외). 본문 실험은 **Lean 3** 기준이고 Lean 4 결과는 부록 D 에 있음.
- 공유일: 2026-10-10 · 발표: 2026-10-11 W02

## 한 줄 요약

Lean 증명을 **"증명 상태 → tactic → 새 증명 상태"** 의 반복으로 보고, 이를 프로그램이 다룰 수 있게 만든 오픈소스 도구·데이터·모델 모음. 정리 증명의 핵심 병목을 **premise 선택 (필요한 기존 정리 찾기)** 으로 보고, 검색으로 premise 를 골라 tactic 을 만드는 **ReProver** 를 제안함.

## 1. 논문을 읽기 위한 Lean 기본 개념

| 개념 | 뜻 | 내가 공부한 예 |
| --- | --- | --- |
| **증명 상태 (state)** | 지금 쓸 수 있는 가정 + 증명해야 할 목표 (`⊢`) | MIL 2.3 Infoview: `h₀ : a ≤ b, h₁ : b < c ⊢ a < c` |
| **tactic** | 증명 상태를 바꾸는 명령. 인자를 받고 서로 조합 가능 | `rw`, `apply`, `exact`, `linarith` |
| **premise** | tactic 이 가져다 쓰는 기존 정리·정의 | `lt_of_le_of_lt`, `mul_comm` |
| **증명 트리** | 처음 명제(뿌리)에서 tactic(간선)으로 상태를 쪼개 모든 목표가 풀릴 때까지 | 웜업 14번: `key` 를 `constructor` 로 두 갈래로 나눔 |
| **mathlib** | premise 가 모인 Lean 수학 라이브러리 | `Mathlib.Data.Real.Basic` |

```lean
example (a b c : ℝ) (h₀ : a ≤ b) (h₁ : b < c) : a < c := by
  -- 상태: h₀ : a ≤ b, h₁ : b < c ⊢ a < c
  exact lt_of_le_of_lt h₀ h₁   -- tactic: exact, premise: lt_of_le_of_lt
  -- 상태: 목표 없음 → 증명 끝
```

**왜 premise 가 어려운가 (논문 3장)**: 증명에 쓸 수 있는 정리는 라이브러리에 수십만 개. 그런데 아무거나 쓸 수는 없고, **이미 정의되어 있고 현재 파일에서 import 된 것** 만 쓸 수 있음. 사람도 기계도 "지금 여기서 쓸 정리" 를 고르는 게 가장 어려움.

논문 예: `gcd n n = n` 증명에서 `rewrite mod_self` 의 `mod_self` (n % n = 0) 는 **다른 파일에 정의된 premise**. 이걸 알아야 증명이 진행됨.

## 2. LeanDojo: 도구와 벤치마크 (4장)

**(1) 데이터 추출**: 코드에는 안 보이는 정보를 뽑아냄
- 파일 의존 관계(import 그래프)와 각 파일의 구문 트리
- 모든 tactic 과 **그 앞뒤 증명 상태** → 증명 트리 복원 가능
- premise 마다 **정의된 위치와 쓰인 위치**, 축약 이름(`mod_self`)의 전체 이름(`nat.mod_self`)

**(2) Lean 과 상호작용**: Lean 을 gym 같은 환경으로 만듦
- `initialize(theorem)` → 처음 증명 상태
- `run_tac(state, tactic)` → 다음 상태 또는 에러 상태 (시간 초과, 적용 불가 등)
- 기존 도구는 맞는 증명의 **21.1% 를 틀렸다고 오판** → LeanDojo 는 **1.4%** 로 줄임

**(3) LeanDojo Benchmark** (mathlib 에서 추출)

| 항목 | 수 |
| --- | --- |
| 정리·증명 | 98,734개 (Lean 파일 3,384개) |
| premise | 130,262개 |
| tactic | 217,776개 (그중 premise 를 하나 이상 쓰는 것 129,243개, 평균 2.13개) |
| train / val / test | 94,734 / 2,000 / 2,000 |

**`novel_premises` 분할**: mathlib 에는 거의 같은 증명이 붙어 있는 정리가 많아서(예: `conj_conj_mul`, `conj_mul_conj` 모두 `rw [conj_mul, conj_conj]`), 무작위로 나누면 **외워서 푸는** 문제가 생김. 그래서 테스트 증명이 **학습에 한 번도 안 나온 premise** 를 적어도 하나 쓰도록 나눔.

## 3. ReProver: 검색 + 생성 (5장)

```
증명 상태 ─▶ [Retriever] 접근 가능한 premise 중 100개 검색
         ─▶ [Generator] 상태 + premise 100개를 이어 붙여 tactic 후보 여러 개 생성
         ─▶ Lean 에서 실행 ─▶ 새 상태 ─▶ best-first search 로 반복
```

- **Retriever**: Dense Passage Retriever 기반. 상태와 premise 를 같은 벡터 공간에 넣고 코사인 유사도로 순위. premise 벡터는 미리 계산해 두므로 빠름.
- 개선 1. **접근 가능한 premise 만 검색**: 후보가 평균 130K → **33K** 로 줄어 검색이 쉬워짐.
- 개선 2. **같은 파일의 premise 를 오답 예시로 학습 (in-file negatives)**: 정답과 같은 파일에 있는 비슷하지만 틀린 premise 를 구별하도록 학습.
- **Generator**: 공개 모델 ByT5-small (299M) 을 사람이 쓴 tactic 으로만 미세조정. 수학 전용 사전학습·비공개 데이터·강화학습 없음.
- 학습 비용: **A100 GPU 1장으로 5일 (약 120 GPU 시간)**. 기존 방법은 1,000 GPU 시간 이상.

## 4. 결과 (6장)

**정리 증명 성공률 (Pass@1, 한 번의 시도·10분 제한)**

| 방법 | random | novel_premises |
| --- | --- | --- |
| `tidy` (mathlib 의 규칙 기반 tactic) | 23.8% | 5.3% |
| GPT-4 (zero-shot, tactic 35개 생성) | 29.0% | 7.4% |
| **ReProver** | **51.2%** | **26.3%** |
| ReProver, 검색 없이 | 47.6% | 23.2% |

- 검색을 붙이면 두 분할 모두 성공률이 오름 → **premise 검색이 실제로 도움**.
- 모든 방법이 `novel_premises` 에서 크게 떨어짐 → 처음 보는 정리를 찾아 쓰는 것이 진짜 어려운 부분.
- premise 검색만 따로 봐도(R@10) random 38.4%, novel_premises 27.6% 로 BM25 키워드 검색(17.2%, 15.5%)보다 좋음.
- 학습에 없던 데이터셋: MiniF2F 26.5%, ProofNet 13.8%. Lean 증명이 없던 정리 MiniF2F 33개, ProofNet 39개를 새로 증명.

## 5. 내 해석 · 우리 프로젝트에 적용할 점

- **웜업 14번 경험과 같은 결론**: 참조 증명 294줄을 56줄로 줄인 핵심은 `card_image_of_injective`, `Fintype.card_set` 같은 **맞는 premise 를 아는 것** 이었음. 논문이 premise 선택을 병목으로 본 것과 같은 지점.
- **"접근 가능한 premise" = 버전 호환**: 대회는 Mathlib v4.25~v4.27 세 버전에서 컴파일돼야 함. "그 버전에 실제로 있는 정리만 후보로 둔다" 는 LeanDojo 의 방식이 호환 점수와 바로 연결됨.
- **외우기 vs 찾아 쓰기**: `novel_premises` 결과처럼, 비슷한 증명을 외운 모델은 처음 보는 정리에서 약함. 리팩터 에이전트도 정리 검색 도구가 필요함.
- **상호작용 루프 = 리팩터링 반복**: `run_tac` 으로 고쳐 보고 에러로 다시 고치는 구조는 손지연 님 P12 리팩터링 기록(1~6차 시도)과 같은 흐름. 이 루프를 자동화하는 것이 에이전트의 역할.
- **한계**: 본문 실험은 Lean 3 기준이라 Lean 4·최신 Mathlib 에 그대로 적용되지는 않음 (Lean 4 결과는 부록 D).
