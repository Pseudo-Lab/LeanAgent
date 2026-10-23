# Escalation 정책과 소규모 검증 데이터 recipe

2026-10-14. 현재 문서는 구현할 검증기의 계약이다. 동봉 Python은 관찰 결과를 입력받아 정책 결정과 프롬프트를 출력하는 오프라인 prototype이며 Lean runner나 점수 계산기는 아니다. 모델 API는 호출하지 않는다.

## 2026-10-15 보완: 판단값의 결정적 정의

이 절이 아래 초안의 모호한 표현보다 우선한다. 기존 `trusted_pre_state=true`, `metrics_complete=true`, 자유서술 `optimization_evidence`만으로는 판단하지 않는다. 이 입력을 제거하거나 무시하도록 Python을 수정했다. 다음 규칙은 LLM 없이 실행하지만, 개선 가능성을 수학적으로 보증하는 규칙은 아니다.

### 명제와 답 고정

여기서 답은 결론에 명시된 값/식/관계이며, 증명 본문은 바꿀 수 있다. `answer = 42`를 증명하는 문제를 `answer = 43` 또는 가정을 추가한 정리로 바꾸면 즉시 reject한다. 원본 proof도 baseline으로 불변 보관한다.

1. 신뢰하는 runner가 원본 파일과 대상 body의 정확한 parser 범위를 고정한다. 모델이 범위를 지정할 수 없다. 원문 전체, 환경 lock, 원본 proof를 baseline artifact로 보관한다.
2. 후보는 body만 받는다. 새 파일은 `원문 prefix + 후보 body + 원문 suffix`로 구성한다. 전체 파일 제출이라면 이 결과와 정확히 일치해야 한다. statement·binder·답·imports·주변 정의의 공백 변경조차 이 단계에서는 허용하지 않는다. Python `immutable_contract`가 이를 검사한다. offset은 Python 문자열 문자 단위이며 Lean의 byte offset을 adapter에서 변환해야 한다.
3. 이 문자열 검사는 필요조건이다. 후보 body가 새 command를 끼워 넣거나 comment로 뒤쪽을 삼키는 경우를 막으려면 Lean adapter에서 단일 proof term 범위, command 구조와 주변 declaration 보존, 고정된 정리 타입에 대한 전체 elaboration/kernel 검사, sorry/금지 구성 및 허용 axiom 검사가 추가로 필요하다. prefix/suffix 일치만으로 최종 승인하지 않는다.
4. 버전별 원본 환경에서 같은 타입을 증명해야 한다. 환경 변경으로 정리 의미를 바꿀 수 없도록 toolchain/dependencies/주변 source hash를 함께 고정한다. 최종 검증이 없으면 eligible=false이다.

현재 Python에는 2번 문자열 계약 검사가 구현되어 있다. 1/3/4의 Lean 수집·검사 adapter는 아직 구현 전이다. 따라서 지금 prototype만으로 명제 보존/정당성 검증이 완성됐다고 주장하지 않는다.

### ‘실패 직전 상태가 확실함’ → 재실행으로 확인된 상태

runner가 아래 모두를 충족한 인증 자료를 만들 때만 작은 범위 수리를 허용한다.

- 인증 자료의 candidate hash가 현재 body SHA-256과 일치하고 environment hash도 일치한다.
- snapshot은 실패한 tactic 실행 직전에 캡처했다.
- 깨끗한 동일 환경에서 prefix를 재실행했고 오류 수가 0이다.
- 오류 복구용 placeholder를 사용하지 않았으며 sorry가 없다.
- 재실행 전후 비교한 goal/context 상태의 digest가 같다.

하나라도 없거나 불일치하면 전체 body 범위로 요청하고, 추론해서 만든 goal을 검증된 상태로 전달하지 않는다. 상태 digest는 goal·local context·metavariable 할당을 포함하고 실행별 임시 ID를 일관되게 정규화해야 한다. 이 정규화/인증 자료 생성은 Lean adapter 구현 사항이다. Python `state_is_replayable`은 자료의 조건을 검사한다. 모델이 인증 자료를 만들도록 해서는 안 된다.

이 인증은 ‘여기까지의 실행을 재현했다’는 뜻이다. `left` 같은 앞선 선택이 적절하거나 현재 goal이 해결 가능하다는 뜻은 아니다. 작은 범위 요청에서도 원인이 앞부분이면 모델이 더 넓은 변경을 제안할 수 있고 전체를 재검증한다.

### ‘구체적인 개선 여지’ → 숫자로 정한 추가 탐색 예산 배정

실제 개선 가능성을 LLM 없이 확실하게 판정하는 일반 알고리즘은 전제하지 않는다. 표현을 바꾸어, 다음은 **추가 모델 시도에 예산을 쓸 조건**으로 정의한다.

먼저 baseline/candidate token·HB가 유효하고, 모든 지정 버전 검사가 완료되고, 현재 candidate/environment hash에 맞으며 incumbent와 같은 계측 방식인지 확인한다. 없으면 MEASURE. 양의 baseline 분모만 지원하고 0이면 별도 공식 규칙 확인 전 계산하지 않는다.

로컬 추출/수리 시도가 끝난 valid 후보에서 다음 중 하나면 optimization 요청 대상으로 삼는다.

1. 계산한 combined가 incumbent 점수 이하이다.
2. candidate HB가 baseline HB의 125% 이상이다.
3. 실제 지정 버전 중 실패한 버전이 있다.

세 조건 모두 아니면 현재 정책은 추가 optimization을 생략하고 selector로 간다. 예산·중복·횟수 gate도 통과해야 실제 프롬프트가 출력된다. 125%는 조정할 초기 heuristic이며 최적임을 주장하지 않는다. 이 정책은 개선 기회를 놓칠 수 있다. 이후 동일 예산 실험으로 ‘개선된 모든 후보에도 추가 시도’ 정책과 비교할 수 있다. `optimization_trigger`가 직접 계산하며 자유서술 근거는 호출 여부를 바꾸지 않는다.

### 남아 있는 adapter 계약

`baseline_verified`, local 목록 소진 여부, duplicate_request, same_failure도 모델의 자기평가 값이면 안 된다. runner가 baseline 인증서, 고정 operator 목록의 실행 기록, 요청 packet hash, 오류코드+정규화 goal/context fingerprint로 각각 산출해야 한다. 아직 Python은 이 네 항목의 생산까지 구현하지 않았다. `localization.scope`는 parser에서 가장 작은 enclosing tactic/block을 찾고, 위치 매핑이 없으면 body로 정한다. 후보의 자기보고와 runner의 관찰을 별도 schema로 분리하는 작업이 다음 구현 단계다.

## 1. 처리 흐름

```text
원본/환경 검증 → candidate body를 원래 위치에 삽입 → 계약 검사 → Lean 검사
  ├─ 환경 실패: 환경 복구, proof 수리 호출 금지
  ├─ 입력 계약 위반: 후보 거부, incumbent 보존
  ├─ proof 실패: 진단/상태 추출 → 작은 범위부터 로컬 수리
  │    ├─ 성공: 전체 재검증 → 아래 valid 경로
  │    └─ 적용할 수리 없음/실패: escalation gate → 프롬프트 출력
  └─ valid: ? 제안 추출/재실행 → 원후보+추출후보 계측
       ├─ 구체적 개선 기회+로컬 시도 완료: optimization gate → 프롬프트 출력
       └─ 그 외: 현재까지 최고 eligible 후보 선택
모델 응답 → 계약 검사부터 동일 경로 재진입; 모든 후보와 incumbent 보존
```

출력 선택은 기존 combined selector 계약을 따른다. 완전하고 비교 가능한 metric을 가진 eligible 후보만 비교하고, 원본보다 엄격한 개선이 없으면 검증된 원본을 반환한다. 오류 개수 감소는 score 개선이 아니다. 모델 요청에는 원래 Arena 입력 proof를 제공할 수 있지만 데이터 제작자의 별도 gold repair는 제공하지 않는다.

## 2. Escalation gate

| 관찰 | 먼저 할 작업 | LLM 조건/범위 |
|---|---|---|
| toolchain/import/build 실패 | 원본을 같은 환경에서 검사, 환경 복구 | proof repair로 escalate하지 않음 |
| 본문 아닌 정리/명제 수정, 금지 construct | 후보 거부 | 자동 수정으로 위반을 숨기지 않음; 다음 생성 요청은 별도 정책 |
| 괄호/들여쓰기/출력 wrapper 오류 | 명백하고 한정된 포맷 수리만 시도 | 파싱 실패로 신뢰할 상태가 없으면 본문 범위 |
| unknown identifier | 문맥에 실제 존재하는 이름과 unification 기반 후보 확인 | 이름 수리 실패 또는 필요한 lemma 자체를 모르면 블록/본문 |
| exact 타입 불일치, 남은 작은 goal | assumption/rfl/exact? 및 목표에 맞는 solver | 실행한 후보와 실패 이유를 제공하고 tactic/블록 |
| 앞선 분기/귀납/보조명제 선택이 문제 | 최근 성공 단계까지 되돌려 블록 재시도 | 구조 변경이 필요하면 블록/본문 |
| heartbeat 초과 | baseline 환경 비교, 한정된 재실행/병목 확인 | 유효성을 모르면 repair; 유효한 계측 완료 후보만 optimization |
| valid지만 비용 큼 | simp?/aesop? 결과 추출, 후보별 재실행·계측 | 명시적인 개선 기회가 남으면 optimization |
| 일부 지정 버전만 실패 | 같은 body와 각 버전 진단 수집 | 공유 body 호환성 개선; 버전별 다른 body 제출 금지 |
| 반복된 동일 실패 | 새 후보 hash/오류/상태를 이력과 비교 | 같은 요청 재전송 금지, 범위를 넓히거나 중단 |

`simp`는 목표를 완전히 닫지 않고 상태만 바꿀 수 있다. 작은 블록이 통과해도 뒤쪽 전체를 replay한다. unknown identifier에 유사 문자열 이름을 무조건 대입하지 않는다. 실패 뒤 복구용 metavariable/sorry가 포함된 상태는 trusted prefix로 사용하지 않는다. 서로 다른 분기라도 metavariable을 공유할 수 있으므로 독립성을 가정하지 않는다.

로컬 시도는 고정 횟수 소진이 아닌 **적용 가능한 수리 목록**으로 정의한다. `pending`은 남은 적용 가능 작업이 있음, `exhausted`는 해당 목록을 실제 실행함, `not_applicable`은 구체적인 이유로 적용할 작업이 없음이다. 각 값에는 실행 로그 또는 이유가 필수다. 무한한 tactic 열거를 전부 소진했다는 의미가 아니다.

## 3. 요청과 중단

- 기본 시작값: 문제당 repair 요청 최대 2회, optimization 최대 1회. 조정 가능한 비용 통제 정책이며 대회 규정이나 검증된 최적값이 아니다. 다른 생성 호출의 비용도 동일 ledger에 합산한다.
- 실제 호출 전 입력 토큰+최대 출력/과금 대상 reasoning token과 가격에 근거한 보수적 비용 상한을 구한다. `spent + reserved + next_upper_bound <= cap`일 때만 호출 가능. 가격/상한이 없으면 PRICE_REQUEST. 병렬 실행 시 실제 caller가 원자적으로 budget을 예약해야 한다.
- 첫 호출 이후 같은 실패라면 tactic→block→body로 확대. 본문 범위에서도 새 정보 없이 반복하면 중단. 오류 개수만 감소했다고 진전으로 보지 않는다.
- `need_context`는 요청된 실제 문맥을 수집한 뒤 재판단한다. 누락 정보를 추측하지 않는다. 이전 API 호출은 이미 비용/횟수에 포함된다.
- 전체 proof hash, 환경 hash, 진단, scope, 제공 문맥이 동일한 요청은 중복이다. 새 정보가 있는 요청까지 candidate hash만으로 차단하지 않는다.
- 계측이 없으면 optimization보다 측정이 먼저다. `aesop`을 썼다는 사실 하나는 optimization_evidence가 아니다. 실제 비용, 제안 추출 실패, 반복 분기나 중복 보조단계 등 구체적 기회를 기록한다.
- baseline 검증 불가이면 정상 fallback 성공이라고 표시하지 않는다. 모델 실패/무응답/예산 소진이어도 검증된 incumbent를 잃지 않는다.

## 4. 프롬프트에 넘길 정보

고정 명제/주변 문맥/환경, 원본 proof, 현재 후보와 hash, 원문 진단 및 위치, 실패 직전 목표·가설, localization 근거와 신뢰 여부, 로컬 시도와 결과, 이전 모델 시도, 비교 가능한 후보 metric, incumbent, 제출 제약을 포함한다. 문맥을 자르면 잘린 범위를 명시한다. 실제로 수집하지 않은 목표나 실패 원인을 만들어 넣지 않는다.

모델은 전체 replacement body를 JSON으로 반환한다. 작은 범위 수리라도 전체 본문을 받으면 문자열 patch의 낡은 offset 문제를 줄일 수 있다. harness는 변경 범위와 명제 보존을 다시 검사하고, 새 본문을 원래 파일의 대상 위치에 삽입한다. target theorem의 기존 증명을 import하여 자기 이름으로 증명하지 못하도록 해야 한다.

실행: `python3 escalation_policy.py request.json > decision.json`. `action=EMIT_LLM_PROMPT`이면 `prompt` 필드가 전달할 실제 텍스트다. 이 파일을 렌더링하는 것만으로 API 지출이 발생하지 않는다. adapter가 observations를 이 계약으로 변환해야 하며, 관찰이 진짜인지 판단하는 역할은 runner에 있다.

## 5. 소규모 데이터: 실제 Lean 8건 + 정책 fixture 4건

| ID | 현실적인 발생 경위 | 확인할 경로 |
|---|---|---|
| R01 | conjunction 분기를 줄이며 h.1/h.2를 잘못 사용 | local 성공, LLM 불필요 |
| R02 | 이미 binder인 가설을 다시 intro하려 함 | 도입부 오류 local 삭제 또는 본문 수리 |
| R03 | simp 규칙을 명시화하다 필요한 규칙 하나 누락 | 목표 관찰, ? 재탐색, 제안 추출 |
| R04 | aesop으로 바꾼 proof에서 명시적 script 추출 | raw/script 재검증·계측, LLM 자동 호출 금지 |
| R05 | disjunction에서 left를 너무 일찍 선택 | 실패 지점보다 앞의 선택까지 되돌림 |
| R06 | 귀납 증명을 줄이며 필요한 generalizing 또는 보조단계 제거 | tactic 수리 실패 시 블록/본문 escalation |
| R07 | simpa/rw에 사용하던 lemma를 현재 import에 없는 이름으로 변경 | 이름 탐색 실패 후 문맥을 포함한 escalation |
| R08 | 한 분기만 고쳤는데 뒤쪽이 기존 goal/가설 이름에 의존 | 국소 성공만 승인하지 않고 full replay |
| P01 | 실제 호출은 없이 예산 부족 상태 입력 | 프롬프트 없음, incumbent 유지 |
| P02 | 동일 요청 반복과 새 진단이 있는 재요청 | 중복 차단 vs 범위 확대 |
| P03 | 환경 오류 및 baseline 미검증 | proof repair 금지, 정상 fallback과 구분 |
| P04 | 가상 metric으로 동점/악화/개선/누락과 모델 실패 | combined 선택·원본 fallback·best 보존 |

R01~R08은 의도한 오류/경로가 **보장되는 사례가 아니다**. Lean과 로컬 수리를 실제 실행해서 관찰대로 라벨링한다. 자동화가 R05/R06까지 해결하면 local_success로 보존하고 실제 escalation이 관찰되는 추가 변형을 찾는다. 예측에 맞추려고 성공을 숨기거나 solver를 몰래 빼지 않는다. R04의 HB 개선도 측정 전에는 미정이다.

최소 4건은 실제 warm-up proof에서 파생하고 나머지는 이해 가능한 작은 예제로 만든다. 같은 정리의 변형은 하나의 그룹으로 관리한다. 12건은 smoke/regression 데이터이며 held-out 성능 평가가 아니다. Mathlib/Aesop이 없는 환경에 없는 tactic을 끼워 넣어 proof 실패로 라벨링하지 않는다.

각 실제 사례는 환경 pin, 원본/후보/별도 gold body, mutation diff, 실제 진단, 가능하면 실제 상태, 로컬 시도, 전체 replay 결과, 기대 정책과 근거, 전달 프롬프트를 보관한다. metrics는 observed/local_estimate/not_measured를 명시한다. 합성 budget/score 값은 별도 P fixture에서만 사용한다. 자세한 제작 요청서는 `gemini-validation-data-request.md`에 있다.
