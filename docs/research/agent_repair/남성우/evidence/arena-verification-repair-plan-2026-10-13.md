# Lean Refactor Arena: 검증·수리 harness 조사와 초안

작성: 2026-10-13, Asia/Seoul. 상태: 문헌·공식 문서 조사에 기반한 설계 제안이며 구현·성능 검증 전이다.

추가 검토 반영: Python 라이브러리와 Lean 연결은 사용자와 합의했다. 구현 순서는 [읽기 쉬운 전체 계획](arena-harness-plan-readable.md)을 기준으로 한다. [LeanFlow·Lean Copilot 검토](leanflow-copilot-review-2026-10-13.md)에서 LeanProbe 시험, 지속 상태, 빠른/최종 검사 분리와 선택적 모델 제안을 추가했다. 이 문서는 세부 기술 계약과 초기 조사 기록이다.

## 먼저 이해할 목표

Harness는 후보 증명을 받아 Lean을 실행하고, 실패를 분류하고, 필요한 경우 수리를 요청하고, 최종 결과를 기록하는 실행 프로그램이다. 검증자는 LLM일 필요가 없다. Lean 실행과 규칙 검사를 하는 일반 코드가 판정을 맡고, LLM은 필요할 때 수정안을 제안한다.

핵심 가설: 동일 모델·동일 API 예산에서, 모든 실패를 모델에 다시 보내는 방식보다 Lean 진단과 제한된 로컬 자동화를 먼저 활용하는 방식이 API 비용 또는 최종 공식 점수를 개선할 수 있다. 아직 실험으로 입증한 주장은 아니다.

closed-source 트랙과 Python 구현을 우선 가정한다. 모델과 orchestration SDK는 교체 가능하게 둔다. 이번 단계에서는 유료 호출, SDK 설치, 대회 제출을 실행하지 않았다.

## 1. 공식 조건에서 확인한 설계 제약

[Space](https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena)와 [공개 UI 소스](https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena/blob/main/app.py)를 확인했다. 표시 revision은 `56aa7b8`. 제출 전 전체 revision/hash를 고정하고 규칙을 재확인한다.

- Closed-source: 문제별 API $3 상한, 공급자 list-price 기준.
- 점수: token 감소율·heartbeat 감소율·동일 proof의 지정 버전 호환 비율의 평균. 실패·미제출·규칙 위반은 0점이다.
- 제출: `name`/`proof` JSONL, 재현 코드, 별도 보고서.
- 프로젝트 문제는 원래 파일 문맥, PutnamBench는 제공 header/Mathlib 환경에서 검사한다.
- `version_info`는 프로젝트 또는 Mathlib revision을 지정한다.
- 제출 proof의 sorry, native_decide, 계측 명령, 구문 확장 등의 금지 규칙을 검사한다.
- 전체 50문제 공개 2026-11-01, 마감 2026-11-08 안내를 재확인한다.

Space는 UI이고 채점 worker는 별도다. 공개 파일 목록에서 worker 구현은 확인하지 못했다. 현지 계측의 공식 결과 일치를 추후 확인해야 한다.

로컬 데이터는 15문제, 다섯 source에서 각 3문제다. 1·2번은 각 단일 버전이다. 이전 검증 기록의 공식 토큰·heartbeat는 미측정이다.

## 2. 프레임워크 조사: orchestration과 Lean 연결을 구분한다

### 상용 모델 생태계 및 에이전트 프레임워크

프레임워크 자체와 모델 API의 비용은 구분해야 한다. SDK를 사용한다고 검증 자체에 모델 호출이 필요한 것은 아니다.

| 후보 | 공식 문서에서 확인한 기능 | 우리 설계에 적용 | 선택 시 유의점 |
|---|---|---|---|
| Claude Agent SDK | PreToolUse/PostToolUse/Stop hook, subagent 지원 | 후보 저장·검증 도구, 종료 전 인증서 확인, 필요시 수리 subagent | Python/TS hook 지원 차이 확인. 광범위한 파일 편집보다 후보 제출 도구를 우선 제공 |
| OpenAI Agents SDK | 도구 기반 specialist 호출과 handoff 등 orchestration | manager가 repair specialist를 도구로 호출하는 구성 | 이 초안은 OpenAI 공식 orchestration 문서 기준이며 상세 hook API는 구현 시 SDK 버전을 고정하고 확인 |
| LangGraph | workflow/agent 분리, checkpoint 저장·재개 | 검증→분류→수리→재검증을 명시적 상태 전이로 구성 | 처음에는 일반 Python으로 충분. 재개·분기 관리가 복잡해지면 채택 |
| OpenHands SDK | 소프트웨어 에이전트, custom tool, local/remote 실행 | 저장소 탐색·편집까지 넓히는 후속 후보 | proof-body 수리만 하는 MVP에는 기능 범위가 넓음 |

출처: [Claude hooks](https://code.claude.com/docs/en/agent-sdk/hooks), [Claude subagents](https://code.claude.com/docs/en/agent-sdk/subagents), [OpenAI 공식 orchestration](https://developers.openai.com/api/docs/guides/agents/orchestration), [LangGraph workflows](https://docs.langchain.com/oss/python/langgraph/workflows-agents), [LangGraph persistence](https://docs.langchain.com/oss/python/langgraph/persistence), [OpenHands](https://docs.openhands.dev/sdk).

제안: 검증 core는 일반 Python 라이브러리로 만들고, orchestration은 얇은 adapter로 연결한다. 처음부터 여러 SDK를 함께 도입하지 않는다. 프레임워크의 선택과 관계없이 최종 acceptance 경로는 하나로 유지한다.

### Lean 실행·증명 상태 연결 도구

| 후보 | 확인한 기능 | 추천 단계 |
|---|---|---|
| `lake env lean` / 대상 module build | 고정 프로젝트 환경의 실제 파일 검사 | 첫 MVP의 최종 검증 경로 |
| LeanInteract | Python, 기존 프로젝트 설정, 메시지·proof state 접근 | 구조화된 피드백 adapter의 첫 후보 |
| Kimina Lean Server | REST, batch 검증, import 캐시·병렬 실행, infotree 추출 | 후보 수가 늘고 검증 throughput이 병목일 때 |
| Pantograph | tactic 단위 실행, proof state/goal 선택, 탐색 지원 | 특정 실패 지점의 상태를 보존·분기하는 후속 연구 |

[LeanInteract](https://github.com/augustepoiroux/LeanInteract), [Kimina 구현](https://github.com/project-numina/kimina-lean-server), [Pantograph 구현](https://github.com/leanprover/Pantograph).

LeanInteract README는 tactic mode가 실험적이며 유효 증명이 잘못 거부될 수 있음을 명시한다. 도구의 내부 상태 검사만으로 최종 통과를 판정하지 않고 실제 파일 컴파일을 거친다. 모든 지정 toolchain과 REPL 구현의 호환성을 도입 전에 실험한다. 초기에는 REPL이 없어도 전체 후보 검사와 오류 로그 수집이 가능해야 한다.

## 3. Literature search와 도입할 아이디어

| 연구 | 원문에서 확인한 핵심 | 채택할 아이디어 / 범위 |
|---|---|---|
| [Lean Refactor, 2026](https://arxiv.org/html/2605.20244v1) | 전략 검색→planner→refactorer→Lean 검증→실패 시 제한된 debugger 수리. 길이·비용·버전의 목적을 구분 | 전략 담당과 수리 담당 인터페이스 분리, 원래 전략 의도 안의 국소 수정, 실패하면 단계 건너뛰기 |
| [APOLLO, 2025, v5](https://arxiv.org/html/2505.05758v5) | 구문 정리, 실패 블록의 임시 sorry, 로컬 solver, 남은 goal 재귀 수리·재조립 | 로컬 자동화 후 어려운 목표만 모델에 전달. sorry 기반 분해와 큰 재귀 sampling은 MVP에 그대로 이식하지 않음 |
| [Learning to Repair Lean Proofs from Compiler Feedback, 2026](https://arxiv.org/html/2602.02990v1) | 잘못된 증명·compiler 진단·수정 증명/설명의 정렬된 데이터, mutation 기반 연구 | 원인 분류와 repair packet, 실패→수리 trajectory 저장, 결함을 주입한 검증 시험 |
| [Kimina Lean Server, 2025](https://arxiv.org/html/2504.21230v1) | REPL 병렬 처리와 import 캐시, batch 피드백 | 준비 환경·import 캐시 재사용, 후보 격리, 검증 worker pool |
| [Pantograph, 2024](https://arxiv.org/html/2410.16429v1) | tactic 상태 단위 상호작용, goal 선택, 연결된 목표의 탐색 | 후속 proof-state 수리. 목표들은 metavariable을 공유할 수 있어 독립 문제처럼 무조건 병렬화하지 않음 |
| [LeanDojo, 2023](https://arxiv.org/abs/2306.15626) | 환경에서 접근 가능한 premise 정보를 이용한 검색 | 존재하지 않는 lemma 오류에 현재 버전에서 접근 가능한 선언을 제공하는 후속 기능 |

이 연구들의 benchmark 성능이 Arena에서도 재현된다는 주장은 하지 않는다. 특히 APOLLO는 로컬 solver만으로 대부분 해결된다고 결론내리지 않는다. 제한된 로컬 자동화와 모델 수리의 결합을 실험할 근거로 사용한다.

현재 역할에 권장 읽기 순서: Lean Refactor §3.3 → APOLLO §3 및 Appendix A → Compiler Feedback 논문의 데이터·오류 유형 → LeanInteract 예제. Kimina/Pantograph는 실행 병목 또는 tactic 상태 요구가 생겼을 때 읽는다.

## 4. 팀의 세 역할을 연결하는 계약

| 역할 | 입력 | 출력 / 책임 |
|---|---|---|
| 구조·전략 | 원본 증명·현재 문맥·과거 결과 | 전략 의도, 후보 proof body, 수정 허용 범위 |
| 검증·수리 (사용자 담당) | 후보와 고정 환경 manifest | 통과 증거 또는 분류된 오류·국소 수정안·재검증 결과 |
| 실행관리·평가·재현 | 후보/검증 이벤트, API 요청·사용량 | 작업 격리, 비용 ledger, 버전 실행, 점수 계산, run 저장·재현 |

검증 담당은 성공/실패의 의미와 검사 순서를 정하고, 실행 담당은 그 검사를 실제 환경에서 실행할 runner를 제공한다. 버전 검사 결과는 검증 담당이 해석하고, 공식 점수 계산·최종 후보 선정은 평가 담당과 공유한다. 검증 코드가 평가 분모나 dataset을 수정하게 하지 않는다.

핵심 interface 제안:

```text
verify(problem, candidate, environment) -> VerificationReport
prepare_repair(problem, candidate, report, strategy) -> RepairRequest
repair(request, budget_reservation) -> Candidate 또는 GiveUp
certify(problem, candidate, required_environments) -> FinalCertificate
```

`VerificationReport`: candidate/context hash, toolchain/repository revision, 명제·범위 보존, 정책 검사, compile 상태, 진단 위치/원문, 미완성 증명 여부, 대상 공리 목록, 실행 시간·timeout, 로그 경로. 가능하면 goals/context를 추가하되 얻지 못하면 null과 이유를 남긴다. 문자열 진단의 goal을 구조화한 것과 REPL의 실제 proof state는 구분한다.

`RepairRequest`: 첫 유의미한 오류, 인접 코드, 필요한 가설/goal, 현재 버전에서 확인한 선언 signature, 전략 의도, 허용 patch 범위, 이미 실패한 수정, 남은 budget. 전체 저장소와 반복된 전체 로그를 매번 보내지 않는다. 진단 축약은 결정적 코드로 먼저 수행한다.

## 5. 검증 파이프라인

1. **기준 환경 확정:** 최신 공식 데이터 snapshot/hash, toolchain, revision, lockfile을 고정. 각 버전에서 원본이 검증되는지 확인한다. 원본 실패는 후보 실패와 구분하여 environment error로 보고한다.
2. **후보 접수:** model이 statement 포함 파일 전체를 편집하는 대신 proof body만 제출하도록 한다. immutable template의 body 위치에 후보를 넣는다. 줄 번호만 믿지 말고 해당 revision의 실제 선언과 anchor를 확인한다.
3. **저비용 사전 검사:** JSON 형식, 후보 중복 hash, 고정 문맥 보존, 공식 금지 검사와 같은 comment/string 처리. 자체 AST 정책과 공식 filter 일치 여부는 별도 시험한다.
4. **원래 문맥에서 컴파일:** project는 격리된 checkout의 실제 대상 파일을 검사한다. 원본 theorem을 import한 뒤 같은 이름/타입을 재선언해 기존 theorem을 그대로 참조하는 잘못된 검증 경로를 피한다. PutnamBench는 제공 header 사용. 반환 코드, error, 미완성 상태를 함께 확인한다.
5. **대상 정리 감사:** 실제 elaborated theorem type와 기준 type을 비교하는 검사를 계획한다. 지원이 없으면 source/template 보존과 한계를 기록한다. #print axioms로 대상 의존성을 확인하며 `sorryAx`를 거부한다. 새 공리 의존성이 생기면 별도 보고한다. 공리 목록 동일만으로 전체 유효성 판정을 대체하지 않는다.
6. **로컬 수리 또는 모델 수리:** 실패를 아래 분류로 보낸다. 수리 후보도 2~5번을 다시 거친다.
7. **최종 후보 인증:** 같은 proof body로 모든 version_info 환경에서 검사하고, 수정된 모듈과 직접 관련 사용처를 확인한다. 완전 호환이 아니면 실패 버전을 보고하며 자동으로 전체 후보를 버리지 않는다. 공식 정책에 맞는 compatibility 비율로 평가한다.
8. **지표 전달:** final candidate 및 원본을 같은 측정 방식으로 비교. dependencies/import 캐시는 재사용할 수 있으나 이미 만들어진 target .olean을 재생한 wall time을 후보 elaboration 비용으로 쓰지 않는다. 토큰/heartbeat 측정은 공식 worker와 교차 검증 전에는 local estimate로 표시한다.

성공 조건은 단순 `exit=0`이 아니라 규칙·문맥 보존, 실제 완료, 대상 공리 검사, 지정 환경 결과를 포함한다. 기존 다른 정리의 sorry 경고는 대상 정리의 sorryAx와 구분한다.

## 6. 오류 분류와 API를 쓰기 전 할 일

| 오류 | API 없이 가능한 처리 | 모델에 보낼 조건 |
|---|---|---|
| markdown fence/응답 포장 | 명확한 wrapper만 제거하고 원문/변경 기록 저장 | 의도 불명확하거나 Lean parse 오류가 남음 |
| 문법/들여쓰기 | 오류 위치 추출. broad regex rewrite는 피함 | 구문 수정이 필요함 |
| unknown constant/namespace | 동일 버전의 declaration 존재·접근 가능성 조회 | 정확한 대체 후보가 확정되지 않음 |
| type mismatch | expected/actual, 관련 가설과 코드 범위 수집 | 값/타입/인수 순서 수정이 필요함 |
| unsolved goals | 유효한 상태를 얻을 수 있으면 제한된 tactic 후보 시도 | 현재 가설·goal로 로컬 시도 실패 |
| timeout/heartbeat | process 정리, 동일 hash 재실행 방지, baseline과 비교 | 증명의 계산 비용을 줄이는 수정이 필요함 |
| import/toolchain/checkout | 환경 복구 또는 blocked로 분류 | proof repair 모델에 보내지 않음 |
| 정책/명제 변경 | 즉시 거부, 허용된 body 범위로 되돌림 | 전략 담당이 새 적법 후보를 만들어야 함 |

로컬 tactic 예: `assumption`, `rfl`, `simp`, `simp_all`; 환경에 이미 존재하는 경우만 `aesop`, `omega`, `ring` 등을 추가한다. 각각 별도 상태/후보에서 timeout과 heartbeat 한도를 두고 시험한다. 실패한 tactic을 원본에 계속 누적하지 않는다. solver가 성공하더라도 전체 후보의 실제 파일 검증·측정을 다시 한다.

로컬 수리의 범위는 오류 해소다. 전체 증명을 다른 전략으로 바꾸는 것은 전략 담당으로 되돌린다. 자동화가 API 비용을 아끼면서 제출 heartbeat를 늘릴 수도 있으므로 결과는 평가 담당에 전달한다.

## 7. Hooks와 수리 subagent 설계

SDK와 무관한 core 이벤트: candidate_created, verification_finished, repair_requested, repair_finished, candidate_selected. hook은 이 이벤트를 연결하는 adapter이며, validator 자체의 대체물이 아니다.

Claude adapter 예:

- **PreToolUse:** candidate 제출 도구는 body만 허용. 임의 파일 편집 경로를 열지 않고, 정책 위반은 검증 core에서 거부한다.
- **PostToolUse:** 후보 변경 시 hash 기준 검사/캐시 결과를 붙인다. 동일 변경으로 중복 검증·모델 호출을 만들지 않는다. 부분 편집마다 전체 빌드를 수행하는 대신 완성된 candidate 이벤트에서 검사한다.
- **Stop/SubagentStop:** 최신 후보 hash에 일치하는 인증서가 있어야 final candidate가 될 수 있다. 실패 시 무한 stop hook 반복 대신 제한된 수리/실패 결과로 종료한다.

LLM repair specialist는 처음에는 하나만 사용한다. 별도 대화에서 repair packet만 받아 국소 patch 또는 give_up을 반환한다. 환경 설정, statement, import, validator는 수정할 수 없다. specialist의 판단은 성공 인증서가 아니며 patch 적용 뒤 Lean이 다시 검사한다.

LLM 진단 agent와 LLM 검증 agent를 별도로 항상 호출하지 않는다. 진단 축약·판정은 일반 코드, 수정 제안은 repair model이 맡는다. 여러 전략을 병렬 탐색하는 subagent 확장은 다음 단계의 비교 실험으로 남긴다. 모든 LLM subagent 호출 비용은 같은 문제 budget에 합산한다.

## 8. 예산·실행 관리와 연결

트랙 확정 후 정정: closed-source의 공식 제한은 API 지출이다. 확인한 공개 규칙에는 로컬 Lean 검증 횟수나 총 실행 시간/하드웨어 제한이 없다. 아래 로컬 실행 설정과 기록은 개발 효율·프로세스 관리용이며 공식 필수 보고나 compute 상한이 아니다. Lean 실행을 폭넓게 활용한다. 최종 proof의 heartbeat 채점은 탐색 중 총 검증 시간과 별개다.

제안 초기 값(공식 규칙이 아닌 조정할 설정): 후보당 모델 수리 최대 2회, 첫 round 로컬 tactic 후보 최대 8개, 후보당 검증 timeout 60초, 필요 시 120초로 재설정. 실제 원본 측정 뒤 문제별로 조정한다. Lean 실행 횟수와 CPU 시간도 기록한다.

문제별 API hard cap은 공식 $3. 내부 soft cap은 예컨대 $2.70으로 두고 남은 여유를 보존한다. 호출 전에 input/context와 최대 output/추론 token 비용을 예약하고 완료 후 usage로 정산한다. 공급자 list-price 및 cache/추론 token 정책을 manifest에 저장한다. $0.30 여유만으로 초과 방지가 보장되는 것은 아니며, atomic reservation과 호출별 upper bound가 필요하다. 사용량을 알 수 없는 실패 호출도 누락하지 않는다.

cache key: theorem ID, 전체 template/context hash, candidate body hash, repository/dependency revisions, toolchain, verifier config 및 policy version. 모델 수리 중복 방지에는 오류 fingerprint와 실패 patch 기록도 사용한다.

best valid candidate는 별도 보관한다. 검증된 원본도 fallback 후보로 평가할 수 있다. 원본과 같다고 전체 점수가 무조건 0인 것은 아니다. 실제 compatibility와 공식 산식으로 결정한다. 최종 선택은 가장 짧은 proof가 아니라 공식 세 축을 고려한다.

## 9. 구현 순서와 완료 기준

### M0 — API 0달러 검증기

산출물: immutable problem manifest, 격리 파일 조립, CLI runner, VerificationReport JSON, failure 분류, 인증서/로그 저장, mock candidate 입력 CLI.

1·2번 원본/리팩터링 proof를 각각 넣어 확인한다. 검증기 자체의 의미 있는 시험은 unknown identifier, 미완성 goal, statement 변조, sorry, 금지 패턴, timeout을 주입하여 올바른 분류와 거부를 확인하는 것이다. 임시 파일과 사용자의 작업 checkout은 분리한다.

완료 기준: model/API key 없이 실행 가능. `sorry` 때문에 exit code가 0인 후보도 거부. 후보가 자기 원본 theorem을 참조해서 통과하지 못함. 환경 실패가 proof 실패로 분류되지 않음. 후보/hash와 인증서가 일치.

### M1 — 로컬 자동화 수리

산출물: LeanInteract adapter의 toolchain compatibility spike, 목표/가설 추출, 제한된 tactic 후보, patch와 전체 재검증. REPL 미지원 환경은 CLI-only 기능으로 명확히 표시한다.

완료 기준: 성공/실패/timeout으로 만든 고정 fixture에서 상태 복구와 후보 격리가 작동. 로컬 수리로 만든 최종 proof에 sorry가 없음. 원본 프로젝트 문맥에서 다시 통과.

### M2 — 모델 수리와 한 가지 SDK 연결

산출물: repair packet, provider adapter, 제한된 specialist 호출, 비용 예약 interface, 동일 실패 반복 방지. Python core+직접 API baseline을 먼저 만들고 팀이 선택한 Claude/OpenAI/LangGraph adapter 하나를 연결한다.

완료 기준: mock API와 작은 실제 실험을 구분. 관련 코드만 수정. 호출별 비용 기록. 실패하면 best valid를 보존. 최신 hash를 검증하지 않고 종료 성공으로 표시하지 않음.

### M3 — 버전·공식 평가·재현 연결

산출물: version matrix 결과, 공식 측정 adapter 또는 차이가 표시된 local estimate, 제출 JSONL export, 재현 README/고정 설정/전체 trace.

1·2번 외에 version_info가 여러 개인 문제를 추가한다. 버전마다 다른 proof를 제출하는 방식은 zero-shot 호환성 평가가 아니므로 같은 body를 사용한다. 공식 worker 설정·tokenizer·heartbeat 계측이 확보되면 결과를 비교하고 차이를 해결한다.

### M4 — 수리 설계의 비교 실험

동일한 초기 후보, 모델, 문제별 API cap, local compute 한도를 고정하고 비교한다.

- A: 전체 후보 + raw compiler feedback으로 모델 수리.
- B: 같은 수리 budget + 구조화된 진단 packet.
- C: B + 제한된 로컬 tactic/결정적 수리.
- D(선택): C + 격리된 repair subagent. B/C의 효과와 context isolation 효과를 구분한다.

주요 지표: 검증 성공률, 공식 점수(또는 local estimate라고 표시한 점수), 문제별 total/max API spend, 수리 성공당 비용. 보조 지표: 수리 호출 수, Lean 실행 수/CPU·wall time, 오류 유형별 개선, token/heartbeat/compatibility. 성공한 문제만 골라서 평균내지 않는다. 15 warm-up 문제에 맞춘 개발과 일반화 성능의 평가는 구분한다.

## 10. 남은 확인 사항과 바로 다음 행동

1. 팀이 사용할 모델/provider와 언어 확정: 이 문서는 Python, closed-source 가정.
2. 실행 담당과 manifest/runner API를 맞추고, 전략 담당과 body-only candidate/허용 patch 범위를 맞춘다.
3. 최신 benchmark와 공개 UI 규칙을 snapshot으로 고정하고 official worker/측정 코드 공개 여부를 운영자 자료에서 확인한다.
4. 첫 개발은 M0으로 시작한다. SDK나 multi-agent를 먼저 설치하지 않아도 검증·수리 담당의 핵심 기여를 독립적으로 만들 수 있다.

이번 조사는 프레임워크 문서, 논문 원문/초록 및 공개 Arena 소스를 읽은 범위다. 도구 설치·버전 호환 시험·harness 구현·유료 API 실험은 아직 수행하지 않았다.
