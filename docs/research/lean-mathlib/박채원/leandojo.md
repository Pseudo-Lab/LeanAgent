# LeanDojo: Lean 기본 개념으로 읽는 정리 증명 환경

- 분야: `Lean&Mathlib` (`Automated Theorem Proving`, `Verifier-guided Agent` 태그도 있음)
- 논문: Kaiyu Yang et al., [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](https://arxiv.org/abs/2306.15626v2), NeurIPS 2023 Datasets and Benchmarks Track
- 코드: [LeanDojo](https://github.com/lean-dojo/LeanDojo), [ReProver](https://github.com/lean-dojo/ReProver) (MIT License)
- 참고 영상: [Alex Gu, *Proving and Improving* (MERL 세미나)](https://www.youtube.com/watch?v=odd0jL02Be8) — LeanDojo 공저자가 LeanDojo 와 후속 연구 ProofOptimizer 를 설명
- 정리 범위: 논문 본문 1~7장 + 영상. 본문 실험은 **Lean 3** 기준 (Lean 4 결과는 부록 D, 영상에 따르면 Lean 3·4 벤치마크를 따로 만듦)
- 공유일: 2026-10-10 · 발표: 2026-10-11 W02

## 한 줄 요약

Lean 증명을 **"증명 상태 → tactic → 새 증명 상태"** 의 반복으로 보고, 이를 프로그램이 다룰 수 있게 만든 오픈소스 도구·데이터·모델 모음. 정리 증명의 핵심 병목을 **premise 선택 (필요한 기존 정리 찾기)** 으로 보고, 검색으로 premise 를 골라 tactic 을 만드는 **ReProver** 를 제안함.
영상 후반의 **ProofOptimizer** 는 "이미 맞는 증명을 짧게 만드는" 연구로, 우리 대회(Lean Refactor Arena)와 과제가 거의 같음.

---

## 1. Lean 기본 개념: `gcd n n = n` 예제로

논문 그림 1·2 와 영상 앞부분이 같은 예제로 설명함.

```lean
theorem gcd_self (n : nat) : gcd n n = n :=
begin
  cases n,             -- n = 0 인 경우와 n = k + 1 인 경우로 나눔
  { unfold gcd },      -- gcd 0 0 : 정의대로 펼치면 끝
  unfold gcd,          -- gcd (k+1) (k+1) = gcd ((k+1) % (k+1)) (k+1)  (유클리드 호제법)
  rewrite mod_self,    -- premise mod_self : n % n = 0  (다른 파일에 정의됨)
  apply gcd_zero_left  -- premise gcd_zero_left : gcd 0 x = x
end
```

| 개념 | 뜻 | 위 예제에서 |
| --- | --- | --- |
| **증명 상태 (state)** | 지금 쓸 수 있는 가정 + 증명해야 할 목표 (`⊢`) | `k : ℕ ⊢ gcd (k+1) (k+1) = k+1` |
| **tactic** | 증명 상태를 바꾸는 명령. 인자를 받고 조합 가능 | `cases`, `unfold`, `rewrite`, `apply` |
| **premise** | tactic 이 가져다 쓰는 기존 정리·정의 | `mod_self`, `gcd_zero_left` |
| **증명 트리** | 처음 명제(뿌리)에서 tactic(간선)으로 상태를 쪼개 모든 목표가 풀릴 때까지 | `cases n` 에서 두 갈래로 나뉨 |

- `cases n` : 자연수는 `0` 이거나 `k + 1` → 목표가 두 개로 갈라짐.
- `0` 쪽은 `gcd` 정의만 펼치면 끝 (`unfold`).
- `k + 1` 쪽은 정의를 펼치면 유클리드 호제법 꼴이 되고, `mod_self` 로 `(k+1) % (k+1)` 를 `0` 으로 바꾼 뒤 `gcd_zero_left` 로 끝냄.

**왜 premise 가 어려운가**: premise 는 **이미 정의되어 있고 현재 파일에서 import 된 것** 만 쓸 수 있음 (`gcd_self` 를 증명할 때 아직 정의 안 된 정리는 못 씀). 그런데 라이브러리에 정리가 수십만 개라서, 사람도 기계도 "지금 여기서 쓸 정리" 를 고르는 게 가장 어려움.

> MIL 2.3 으로 보면: `exact lt_of_le_of_lt h₀ h₁` 에서 tactic 은 `exact`, premise 는 `lt_of_le_of_lt`. 웜업 14번에서 `key` 를 `constructor` 로 두 갈래로 나눈 것도 증명 트리의 분기임.

---

## 2. LeanDojo: 데이터 추출과 상호작용 (논문 4장)

### 2.1 데이터 추출: 코드에 안 보이는 정보를 뽑음

GitHub 의 Lean 파일에는 **증명 상태가 적혀 있지 않음** (사람은 VS Code Infoview 로만 봄). LeanDojo 는

1. 파일을 **구문 트리(AST)** 로 파싱 → 각 tactic 이 증명의 어느 갈래에 있는지 파악
2. 코드를 **실제로 실행**(Lean 메타프로그래밍)해서 tactic 앞뒤의 증명 상태를 기록 → 증명 트리 복원
3. premise 마다 **정의된 위치와 쓰인 위치** 기록 (같은 파일인지, import 한 다른 파일인지). 축약 이름 `mod_self` 의 전체 이름 `nat.mod_self` 도 기록

영상 설명: 공개된 아무 Lean 저장소(GitHub URL)를 넣으면 **traced repo → traced file → traced theorem** 구조를 만들고, 여기서 파일 의존 관계·premise·tactic·상태를 꺼내 벤치마크를 만들 수 있음. mathlib 말고 다른 저장소에도 쓸 수 있음 (후속 연구 LeanUniverse).

### 2.2 프로그램으로 Lean 과 상호작용

Lean 을 gym 같은 환경으로 만듦.

- `initialize(theorem)` → 처음 증명 상태
- `run_tac(state, tactic)` → 다음 상태 또는 에러 상태 (시간 초과, 적용 불가 등)
- 기존 도구는 맞는 증명의 **21.1% 를 틀렸다고 오판** → LeanDojo 는 **1.4%**

### 2.3 LeanDojo Benchmark (mathlib 에서 추출)

| 항목 | 수 |
| --- | --- |
| 정리·증명 | 98,734개 (Lean 파일 3,384개) |
| premise | 130,262개 |
| tactic | 217,776개 (그중 premise 를 하나 이상 쓰는 것 129,243개, 평균 2.13개) |
| train / val / test | 94,734 / 2,000 / 2,000 |

**`novel_premises` 분할**: mathlib 에는 거의 같은 증명이 붙은 정리가 많아서 (예: `conj_conj_mul`, `conj_mul_conj` 둘 다 `rw [conj_mul, conj_conj]`) 무작위로 나누면 **외워서 푸는** 문제가 생김. 그래서 테스트 증명이 **학습에 한 번도 안 나온 premise** 를 적어도 하나 쓰도록 나눔.

---

## 3. ReProver: 검색 + 생성 (논문 5장)

```
증명 상태 ─▶ [Retriever] 접근 가능한 premise 중 100개 검색
         ─▶ [Generator] 상태 + premise 를 이어 붙여 tactic 후보 여러 개 생성
         ─▶ Lean 에서 실행 ─▶ 새 상태 ─▶ best-first search 로 반복
```

**왜 검색이 필요한가 (영상)**: 상태만 보고 tactic 을 만드는 모델은 premise 이름을 **외워서** 써야 함 → 학습 때 못 본 premise 는 못 씀.

**Retriever**
- 상태와 premise 를 같은 벡터 공간에 넣고 코사인 유사도로 순위. premise 벡터는 미리 계산해 두므로 빠름.
- **대조 학습 (contrastive learning)**: 실제로 쓰인 premise(양성, 예: `mod_self`)는 상태와 가깝게, 관련 없는 premise(음성)는 멀게 학습.
- 개선 1. **접근 가능한 premise 만 검색**: 후보가 130K → 평균 **33K**.
- 개선 2. **같은 파일의 premise 를 음성으로 (in-file negatives)**: 영상 예시로 `mod_self` 가 정답일 때 `mod_one` 처럼 **비슷해 보이지만 쓸모없는** premise 를 음성으로 줘야 모델이 진짜로 구별하는 법을 배움 (hard negative).

**Generator**: 공개 모델 ByT5-small (299M) 을 사람이 쓴 tactic 으로만 미세조정. 수학 전용 사전학습·비공개 데이터·강화학습 없음. 학습은 **A100 1장으로 5일 (약 120 GPU 시간)**, 기존 방법은 1,000 GPU 시간 이상.

---

## 4. 결과 (논문 6장)

**정리 증명 성공률 (Pass@1, 한 번의 시도·10분 제한)**

| 방법 | random | novel_premises |
| --- | --- | --- |
| `tidy` (mathlib 의 규칙 기반 자동화) | 23.8% | 5.3% |
| GPT-4 (zero-shot, tactic 35개 생성) | 29.0% | 7.4% |
| **ReProver** | **51.2%** | **26.3%** |
| ReProver, 검색 없이 | 47.6% | 23.2% |

- 검색을 붙이면 두 분할 모두 성공률이 오름 → **premise 검색이 실제로 도움**.
- 모든 방법이 `novel_premises` 에서 크게 떨어짐 → 처음 보는 정리를 찾아 쓰는 것이 진짜 어려운 부분.
- premise 검색만 따로 봐도 (R@10) random 38.4%, novel_premises 27.6% 로 BM25 키워드 검색 (17.2%, 15.5%) 보다 좋음.
- 학습에 없던 데이터셋: MiniF2F 26.5%, ProofNet 13.8%.

**영상에서 말한 지금의 의미**: 최신 모델(PutnamBench 를 대부분 푸는 수준)에 비하면 ReProver 는 작고 약함. 그래도 LeanDojo 가 뽑아내는 **증명 상태·AST·premise 데이터는 아직 충분히 활용되지 않았다** 고 봄.

---

## 5. 영상 후반: ProofOptimizer — 맞는 증명을 짧게 만들기

> 영상 발표 내용 기준. 논문 원문은 따로 확인하지 않았음.

**문제의식**: 최신 prover 가 만든 증명은 맞지만 **너무 길고 읽기 어렵고 느림** (예: Seed-Prover 의 IMO 2025 1번 증명은 4,000줄 이상). 강화학습으로 학습한 prover 는 "맞았나/틀렸나" 만 보상으로 받아서, **쓰지도 않는 `have` 문을 잔뜩 넣는** 경향이 있음 → 줄일 여지가 큼.

**과제**: 명제 S 와 증명 P 가 있을 때, Lean 이 여전히 통과하는 더 짧은 증명 찾기. 맞는지는 **Lean 컴파일 통과 여부** 로만 판단.

**지표**
- `min@k` : k개 후보 중 가장 짧은 증명 길이
- `reduction@k` : 최대 길이 감소율 (원래 길이에 따라 의미가 달라서 비율도 봄)
- 길이는 Lean 전용 토크나이저로 셈 (변수 이름 하나 = 토큰 하나 → 이름만 바꾸는 꼼수 방지)

**방법**

| 단계 | 내용 |
| --- | --- |
| 미세조정 | Qwen 2.5 에 LeanDojo 식 증명 상태 데이터 + 자연어·Lean 쌍 학습 |
| 학습 데이터 | 자연어 문제 → 증명 스케치 → 보조정리 추출 → Goedel-Prover 로 증명 생성, 약 145K 개 |
| Expert iteration | 짧게 만든 후보 중 맞고 충분히 짧아진 것만 골라 다시 학습, 반복 |
| 강화학습 (GRPO) | 원래 증명 대비 길이 감소율을 보상으로 |
| 추론 시 | ① 린터로 "아무것도 안 하는 tactic" 제거 ② 테스트 시 강화학습 ③ 반복 축약 (k개 뽑아 가장 짧은 것 → 다시 반복) |

**결과 (영상)**
- MiniF2F 증명 **87%**, PutnamBench 증명 **57%** 감소, Seed-Prover IMO 증명은 많은 계산으로 **약 절반**.
- Expert iteration 은 여러 개 뽑을 때(다양성) 강하고, 강화학습은 한 번에 뽑을 때(정확도) 강함 → 반복 축약에는 expert iteration 모델을 씀.
- 증명이 길수록 줄이기 어려움.
- **짧아진 증명은 대체로 더 빠르지만 항상은 아님**: 3초 → 16초로 오히려 5배 느려진 예도 있음. 추론 시 기준을 길이 대신 **heartbeats** 로 바꾸자 모든 증명이 원래보다 빨라짐.
- 실패한 시도: 틀린 축약을 Goedel-Prover 로 고치게 했더니(proof repair) 원래보다 **더 길게** 고쳐 버림.
- 짧게 만든 증명으로 학습하면 증명 생성 성능도 약간(1~2%p) 오름.

**질의응답에서 나온 한계**: 길이만 줄이면 코드 골프처럼 **읽기 어려워질 수 있음**. 좋은 증명의 기준(읽기 쉬움, 속도, 재사용 가능한 추상화)을 어떻게 수치로 정의할지가 열린 문제.

---

## 6. 포인트 · 우리 프로젝트에 적용할 점

- **대회 = ProofOptimizer 의 과제**: Lean Refactor Arena 는 "맞는 증명을 길이·heartbeat·버전 호환 기준으로 개선" 하는 과제라 ProofOptimizer 와 거의 같음. 길이 지표(토크나이저), 반복 축약, 린터로 쓸모없는 tactic 제거는 바로 써 볼 수 있는 아이디어.
- **웜업 14번 경험과 같은 결론**: 참조 증명 273줄을 56줄로 (명제 포함, 빈 줄·주석 제외) 줄인 핵심은 `card_image_of_injective`, `Fintype.card_set` 같은 **맞는 premise 를 아는 것** 이었음. LeanDojo 가 premise 선택을 병목으로 본 것과 같은 지점.
- **짧음 ≠ 가벼움**: 웜업 15번에서 18개 조건을 펼쳐 `omega` 로 푼 8줄 증명은 10분이 지나도 컴파일이 안 끝났음. 영상의 "3초 → 16초" 사례와 같은 현상 → **길이와 heartbeat 를 같이 측정** 해야 함.
- **"접근 가능한 premise" = 버전 호환**: 대회는 Mathlib v4.25~v4.27 세 버전에서 컴파일돼야 함. "그 버전에 실제로 있는 정리만 후보로 둔다" 는 LeanDojo 방식이 호환 점수와 바로 연결됨.
- **상호작용 루프 = 리팩터링 반복**: `run_tac` 으로 고쳐 보고 에러로 다시 고치는 구조는 손지연 님 P12 리팩터링 기록(1~6차 시도)과 같은 흐름.
- **한계**: 논문 본문 실험은 Lean 3 기준이라 Lean 4·최신 Mathlib 에 그대로 적용되지는 않음.
