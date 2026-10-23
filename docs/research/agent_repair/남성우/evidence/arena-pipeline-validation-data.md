# Arena 파이프라인 검증용 데이터 설계

2026-10-13. 목적은 모델 학습 데이터 생산보다 검증·수리·점수 선택·원본 fallback이 제대로 동작하는지 확인하는 것이다. 아래 개수는 초기 제안이고 실제 데이터 실행/라벨링 전이다.

## 1. 먼저 고정할 출력 계약

출처: [공식 점수 안내](https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena/blob/main/app.py). 공개 UI는 길이 감소율·heartbeat 감소율·zero-shot 버전 호환 비율의 평균을 안내한다. 실제 tokenizer, heartbeat 측정 환경/기준 버전, 반올림·특수 분모 처리는 worker와 확인해야 한다.

일반적인 양의 baseline 분모에서는:

```text
length_reduction = 100 * (1 - candidate_tokens / reference_tokens)
heartbeat_reduction = 100 * (1 - candidate_heartbeats / reference_heartbeats)
robustness = 100 * successful_listed_versions / listed_versions
combined = mean(length_reduction, heartbeat_reduction, robustness)
```

원본의 감소율은 0, 0이고, robustness는 실제 baseline 결과다. 원본이 모든 지정 버전에서 통과하면 combined는 약 33.33이다. 원본 점수를 자동으로 0으로 두지 않는다.

선택 규칙: eligible하고 metric이 완결된 후보 중 최고 combined가 원본보다 엄격히 높으면 그 후보를 선택. 동점·개선 없음·후보 전부 invalid이면 원본. raw 값으로 비교하고 표시용 반올림으로 winner를 고르지 않는다. 불확실한 계측은 재측정하고 local estimate/official-equivalent 여부를 기록한다. baseline 자체가 invalid이거나 환경이 준비되지 않으면 이를 정상 fallback 성공으로 표시하지 않는다.

## 2. 네 묶음을 분리해서 만든다

| 묶음 | 데이터 | 확인할 것 |
|---|---|---|
| 실제 정상 후보 | 원본, 기존 1·2번 리팩터링, 새로 검증한 후보 | 원래 문맥 컴파일·미완성 검출·계측 |
| 오류 주입 후보 | 정상 proof를 한 부분씩 변형 | 실패 분류·국소 수리·명제/규칙 보호 |
| 점수 선택 fixture | 의도적으로 만든 가상 metric/eligibility | combined 비교·tie·fallback·metric 누락 |
| 버전/cache fixture | 동일 proof의 여러 환경과 상태 변경 | robustness·cache 격리·무효화 |

가상 metric을 실제 Lean 측정값과 같은 파일/지표로 섞지 않는다. `measurement_kind=synthetic`를 명시한다. 오류 주입의 기대 종류도 Lean 실행 전에는 `expected_intent`, 실행 후에 `observed_result`로 분리한다.

## 3. 실제 Lean 데이터의 첫 seed

로컬 warm-up에는 15문제가 있다. 먼저 4문제로 범위를 제한한다.

| seed | 이유 |
|---|---|
| 1: substOldPostSubset | 원본과 기존 후보, project-file 문맥, 단일 버전 |
| 2: extractedOldExprInVars | 기존 후보, 귀납 구조와 남은 goal 수리 |
| 3: Core.InitsUpdatesComm | Strata 안에서 지정 버전 3개 검사 |
| 13: putnam_1964_a4 | 별도 header/Mathlib 경로, 지정 버전 3개 |

시작은 이미 환경이 있는 1·2번으로 한다. 3·13번은 해당 checkout과 toolchain이 준비되면 추가한다. dataset snapshot과 repo revision·dependency hash를 고정한다. 로컬 파일이 현재 공식 데이터와 같은지는 실행 전 비교한다.

1·2번 후보는 ‘기존에 correctness가 확인된 예’이지 ‘공식 점수가 개선된 예’로 미리 라벨링하지 않는다. heartbeat/token은 다시 측정해야 한다.

## 4. 오류 주입 방법

각 proof에서 한 번에 한 종류의 변경을 만들어 원본·patch·seed를 저장한다.

| 주입 | 기대 검사 |
|---|---|
| 현재 문맥에 없는 식별자로 한 이름 교체 | unknown identifier |
| 한 tactic 제거 또는 잘못된 인수 제공 | 남은 goal 또는 type mismatch; 실제 결과로 라벨링 |
| proof를 sorry로 교체 | 종료 코드 0이어도 reject |
| 금지 패턴을 실제 code에 삽입 | policy reject |
| 가정/결론 변경 요청 | body-only 인터페이스에서 거부 |
| 원래 target theorem 이름을 후보에서 참조 | 원본 import로 가짜 통과하지 않음 |
| wrapper/JSON 깨짐 | parse/input 오류 |
| 동일 candidate 반복 | 결과 재사용, 불필요한 model call 없음 |

comment/string에 금지어가 들어간 대조군도 만든다. 공식 filter 동작과 비교하며 우리가 더 관대한 parser를 임의로 공식 기준이라고 쓰지 않는다.

timeout은 재현성이 낮은 ‘느릴 것 같은 proof’만으로 라벨링하지 않는다. runner 시험에는 지연을 제어한 subprocess fixture를 별도로 두고, Lean 통합 시험에는 명시적인 resource 설정을 기록한다. setup 실패도 별도 fixture로 시험하여 proof 오류와 구분한다.

mutation이 의외로 통과하면 invalid 라벨을 붙이지 않는다. 검증된 원본을 known-valid repair로 사용할 수 있지만 최적화 의도를 보존한 수리라고 주장하지 않는다. `strategy_preserved`와 `score_improved`는 별도 결과다.

## 5. 점수 선택 데이터: 모델·Lean 없이 먼저 확인

다음은 공식 실행 결과가 아닌 **가상 감소율** 예다. 세 값이 token/HB/robustness 순서일 때:

| 후보 | 세 지표 (%) | combined | 결과 |
|---|---|---:|---|
| 원본 | 0 / 0 / 100 | 33.333… | baseline |
| 매우 짧지만 비쌈 | 40 / -80 / 100 | 20 | 원본보다 나쁨 |
| 균형 후보 | 20 / 30 / 100 | 50 | 개선 |
| 더 짧지만 버전 손실 | 50 / 10 / 66.666… | 42.222… | 개선하나 최고점 아님 |
| 최고 combined | 10 / 50 / 100 | 53.333… | 선택 |
| 가짜 고득점, invalid | 90 / 90 / 100 | 93.333… | 제외 |

별도 case: 후보 없음, 전부 invalid, 전부 baseline 이하, baseline 동점, 표시 반올림만 동점, 높은 점수지만 HB 미측정, robustness 일부 미검사, baseline 분모 0, baseline 미검증, NaN/invalid metric, 새 검증 전에 중단, 오래된 candidate hash의 인증서. 공식 특수 분모 규칙이 미확인인 경우 unsupported로 처리하고 임의 점수를 만들지 않는다.

한 축의 악화만으로 후보를 자동 배제하지 않는 case도 포함한다. 반대로 세 축 중 하나만 보고 winner를 선택하는 버그를 잡는다. 1·2번처럼 지정 버전이 하나인 데이터만으로 robustness 로직을 시험하지 않는다.

## 6. 버전/cache 데이터

자동화 수리 후 최적화 case도 추가한다: correctness 통과/HB 악화, 명시적 script 추출의 token-HB trade-off, 추출 후 버전 실패, 모델 최적화 실패 뒤 best 보존, raw 자동화가 실제 최고점인 경우. [비교 실험 설계](automation-repair-and-optimization.md)는 직접 LLM, 로컬 자동화, 명시적 추출, 후속 모델 최적화를 동일 API cap에서 비교한다.

- 같은 proof body hash를 각 지정 버전에 보낸다. 버전별 다른 수리를 섞지 않는다.
- 실제 version-specific 실패를 발견했을 때만 version-dependent 라벨을 붙인다. 특정 tactic이 구버전에서 실패할 것이라는 추측을 gold로 쓰지 않는다.
- 실패한 후보 뒤에 정상 후보를 넣어 상태 오염을 확인한다.
- 앞부분 문맥/dependency/toolchain을 바꾸고 기존 cache가 무효화되는지 확인한다.
- 목표에서 닫힌 것처럼 보여도 full-file 검사에서 실패하는 후보를 구분한다.

## 7. 저장 형식

문제, 후보, 실행 관찰, 선택 case를 나눈다.

```text
problems.jsonl        원본 데이터와 고정 환경
candidates.jsonl      body/hash, parent, mutation/전략, source
observations.jsonl    실제 compile·axioms·goals·metric·version 결과
selection_cases.jsonl 가상 점수와 expected winner/fallback
traces.jsonl          실패→로컬 수리→모델 수리→재검증
```

필수 구분: baseline/candidate, synthetic/observed, official-equivalent/local-estimate, compile_fail/environment_error/not_run. local time은 선택적 진단 데이터이며 closed 트랙의 공식 상한이 아니다.

## 8. 단계별 데이터 규모와 사용

첫 제안: 1·2번에서 각 6~8개 mutation으로 정상/오류 후보 15~20개, 별도 selection case 12~15개. 모두 API 없이 만든다. 목표는 대량 수집보다 라벨의 정확성과 위험한 가짜 통과를 잡는 것이다.

그 뒤 3·13번으로 project/header/버전 경로를 확장한다. 다른 source 문제를 포함한 작은 frozen regression set을 별도로 정한다. 같은 정리의 mutation을 개발/평가 양쪽에 나누지 않고 theorem 단위로 묶는다. 이미 보면서 설계한 1·2번은 held-out으로 부르지 않는다.

후속 모델 수리 실험은 고정된 initial candidate/diagnostic 세트로 비교한다. Arena 입력으로 주어진 원래 proof는 모델에 제공할 수 있다. 데이터 제작자가 별도로 만든 gold repair와 기대 라벨은 harness 검증용에만 보관하고 모델 prompt에 넣지 않는다. 성공률과 winner/fallback의 정확성, actual combined, 문제별 API 지출을 보고한다. 단순한 fixture 성공률을 대회 일반화 성능으로 주장하지 않는다.

이 단계는 모델 학습용 fine-tuning 데이터 수집이 아니다. 먼저 이 데이터로 검증기·selector가 신뢰할 수 있게 된 뒤, 실제 실패→수리 trajectory를 누적한다.
