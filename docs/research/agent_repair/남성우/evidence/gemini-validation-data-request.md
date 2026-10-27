# Gemini에게 전달할 제작 요청

아래 요청서와 `escalation-policy-and-data-recipe.md`, `escalation_policy.py`, 기존 `arena-pipeline-validation-data.md`를 함께 제공하세요. 실제 Arena seed 파일과 해당 Lean 프로젝트 접근도 필요합니다. 이 요청서는 Gemini 모델의 기능이나 로컬 실행 권한을 전제하지 않습니다.

---

Lean Refactor Arena의 검증·수리 harness를 시험할 작은 데이터를 만들어 주세요. 대규모 생성이 아니라 실제 일어날 법한 실패 8건과 정책 fixture 4건이 목표입니다. 실제 Lean을 실행할 수 있으면 반드시 실행하고, 실행할 수 없으면 검증 완료라고 하지 말고 재현 가능한 초안과 실행 명령만 제공하세요.

## 목표와 고정 계약

2026-10-15 보완: 첨부 정책의 ‘판단값의 결정적 정의’를 우선 적용하세요. statement의 가정/답/결론 변경 거부, source body 범위 밖 변경 거부, 오래된 candidate/environment 인증 자료 거부를 추가 시험하세요. `trusted_pre_state=true`나 서술형 `optimization_evidence`만으로 통과시키지 마세요. 상태는 runner의 깨끗한 prefix replay 자료가 있어야 하며 없으면 body scope입니다. 계측 후 호출은 개선 가능성의 보증이 아니라 정책의 숫자 조건으로 결정합니다. 인증 자료를 합성한 테스트는 P fixture에만 두고 실제 Lean 관찰과 구분하세요. Lean adapter의 단일 term/command 보존 검사가 아직 구현 전이므로 문자열 계약 검사만 통과한 후보를 최종 검증 완료로 표시하지 마세요.

기존 Lean proof를 refactor한 후보를 검사하고 로컬 수리한 후, 해결되지 않을 때 LLM에 escalation합니다. valid 후보는 simp?/aesop? 제안을 추출하여 재실행하고 tokens/heartbeat/robustness로 평가합니다. 가장 높은 combined의 eligible 후보가 원본보다 엄격히 좋을 때만 선택하고, 동점/악화/실패 시 원래 검증된 proof로 fallback합니다. 기존 best는 후속 실패에도 보존합니다.

원래 정리의 statement, imports, dependencies, project context는 고정합니다. repair를 위해 명제나 환경을 바꾸지 마세요. 모든 지정 버전에는 같은 proof body를 검사합니다. 원래 proof는 모델에 주어도 되는 Arena 입력이고, 제작자가 별도로 만든 gold repair와 expected label은 모델 입력에 넣지 않습니다. gold는 정답 중 하나이지 유일한 정답이 아닙니다.

## 먼저 환경을 확인하세요

1. 실제 seed 위치, 프로젝트, Lean 버전, repo commit, dependency lock/hash, uncommitted context patch를 기록하세요. 버전/파일을 추측하지 마세요.
2. 원본 proof가 원래 문맥에서 통과하는지 확인하세요. 대상 정리 이전 문맥을 사용하거나 원래 위치에 body를 교체하여 검사하고, 기존 target theorem을 import한 환경에서 자기 이름을 참조해 통과시키지 마세요.
3. Aesop/Mathlib의 해당 버전과 사용 가능한 tactic을 확인하세요. 환경이 없으면 BLOCKED_ENVIRONMENT로 보고하세요. 기본 imports를 임의 확장하여 실패를 숨기지 마세요.
4. 제공된 pipeline의 로컬 tactic 목록과 resource 설정을 고정해 저장하세요. 변경이 필요하면 이유와 변경 전후 버전을 남기세요. 케이스별 기대 결과를 맞추려고 목록을 바꾸지 마세요.

## 실제 Lean 사례 8건

첨부 recipe의 R01~R08을 대상으로 만드세요. 최소 4건은 제공된 Arena warm-up 원본에서 파생하고, 나머지는 작은 교육용 정리로 작성할 수 있습니다. 실제 seed가 없으면 필요한 입력을 명시하고 교육용 데이터와 Arena 파생 데이터를 구분하세요.

각 후보의 변형은 현실적인 refactor 행동으로 설명하세요. 예: 분기 순서를 바꿨는데 projection을 그대로 둠, 불필요해 보이는 intro/generalizing/보조단계를 삭제함, 넓은 simp를 simp only로 바꾸다 규칙을 빠뜨림, 유사한 lemma 이름을 잘못 사용함. 무작위 문자열 훼손은 핵심 데이터로 삼지 마세요.

R01 projection 잘못 선택 / R02 첫 intro 오류 / R03 simp only 규칙 누락 / R04 aesop? script 추출 / R05 성급한 left 선택 / R06 귀납 문맥 손실 / R07 사용할 수 없는 lemma 이름 / R08 국소 수리 후 후속 tactic 의존성 실패.

각 사례마다 다음 순서로 실행하세요.

1. seed 원본 검증 로그를 저장합니다.
2. 하나의 명확한 refactor 변형과 diff를 만듭니다. 변형 의도를 expected_intent에 씁니다.
3. 후보를 실제 검사하고 diagnostics의 원문, 위치, 종료 상태를 보관합니다. 실패할 것으로 예상했어도 통과하면 valid로 기록합니다.
4. 연결 도구가 지원하면 실패 직전 goal/hypotheses와 enclosing block을 수집합니다. 수집하지 못했으면 null과 이유를 쓰세요. 사람이 추론한 상태는 inferred로 별도 저장하고 trusted_pre_state로 쓰지 마세요.
5. 고정된 로컬 수리 목록을 실제 실행합니다. 각 후보와 결과를 저장하고, 국소 성공 후에는 반드시 뒤쪽을 포함한 전체 proof를 검사합니다.
6. simp?/aesop?에 대해서는 실제 출력 제안, 해당 위치, 치환된 body와 재검증 결과를 저장합니다. 예상되는 제안을 실제 도구 출력처럼 작성하지 마세요. 원래 raw proof도 보존하세요.
7. 독립적으로 gold repair를 만들고 전체 검증합니다. 가능한 한 refactor 의도를 살리되, 원본 복원만 가능했다면 그 사실을 쓰세요. gold를 로컬 알고리즘에 몰래 주지 마세요.
8. 실제 관찰을 escalation 정책 입력으로 변환하고 `escalation_policy.py`로 decision.json을 생성합니다. EMIT_LLM_PROMPT일 경우 prompt를 prompt.txt에도 저장합니다. 모델 호출은 하지 마세요. 로컬로 해결되면 프롬프트가 없는 것이 정상입니다.
9. 측정할 수 있는 metric만 기록하세요. heartbeat가 어려우면 not_measured로 두고 optimization 판단을 MEASURE로 남기세요. 소스 글자 수를 공식 token 수로 부르지 마세요. 지정 버전 일부만 실행했다면 robustness 완결로 표시하지 마세요.

로컬 자동화가 어려운 사례도 해결하면 그것을 정직하게 기록하세요. 추가 변형으로 실제 escalation 예를 찾되 고정 로컬 목록을 유지하세요. 끝내 escalation 사례가 없으면 이 한계를 보고하세요. 원인 설명과 Lean이 관찰한 사실을 구분하세요.

## 정책 fixture 4묶음

P01 예산 부족/가격 상한 미확인, P02 동일 요청/같은 실패의 scope 확대, P03 환경 오류/baseline 미검증, P04 가상 score 동점·악화·개선·metric 누락/모델 실패 뒤 best 보존을 만드세요.

이들은 synthetic=true로 별도 폴더에 두세요. 각 묶음에 여러 하위 입력을 허용합니다. 정책 renderer가 score selector를 구현하지 않았다는 점을 명시하고, P04의 winner 기대값은 별도 selector 계약을 시험할 데이터로만 제공하세요. 가짜 score나 budget을 Lean 측정값이라고 쓰지 마세요.

## 산출물

```text
validation-mini/
  README.md                     환경, 실행법, 관찰 결과, 한계
  manifest.json                 pipeline 버전, 로컬 tactic 목록, 데이터 출처
  cases/R01...R08/
    case.json                   아래 필드
    original.lean               원래 문맥에서 실행 가능한 파일 또는 원본+적용 patch
    candidate.lean
    gold_repair.lean
    mutation.diff
    logs/                       원문 stdout/stderr/진단과 실행 명령
    attempts/                   시도별 body/로그
    request.json                정책 입력, gold/expected label 제외
    decision.json
    prompt.txt                  EMIT_LLM_PROMPT인 경우만
  policy-fixtures/P01...P04/     합성 입력과 기대 결과
  reproduce.py                  로컬 재실행; 외부 API 호출 없음
```

case.json 필드: id, seed_id, source_kind(arena_derived/toy), source_path, environment, immutable_context_hash, statement, original_body, candidate_body, candidate_hash, expected_intent, observed_result, diagnostics, localization, local_attempts, gold_repair_path, full_replay_result, measurements, expected_route, expected_route_reason, validation_status.

문법적으로 실행 가능한 standalone 파일을 만들 수 없으면 정확한 프로젝트 파일과 body replacement 위치/해시를 사용하세요. 편집된 다른 파일을 덮어쓰지 않도록 임시 checkout/copy에서 재현하세요. 구현 편의를 위해 공개할 수 없는 외부 상태를 몰래 의존하지 마세요.

최종 보고는 사례별 원인/실제 Lean 결과/로컬 수리 결과/escalation 여부/데이터 한계를 표로 정리하세요. 작은 데이터에서 전체 대회 성공률이나 최적 정책이라는 결론을 내리지 마세요.
