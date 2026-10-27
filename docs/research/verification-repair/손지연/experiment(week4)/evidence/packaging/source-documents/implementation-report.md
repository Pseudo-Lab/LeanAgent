# Lean 검증·수리 루프 구현 보고서

작성자: 손지연. 구현 검증 기록일: 2026-10-22. 공유 정리일: 2026-10-24.

`week4/verification-repair`의 재사용 가능한 한 정리 단위 검증·수리 구현을 정리한다. P7 전용 이름·타입·전술 목록에 의존하지 않으며 Python 3.11 이상과 고정된 Lean/Lake 프로젝트를 사용한다. 원래 구현·예제·시험·로그는 [evidence/verification-repair](evidence/verification-repair/)에 내용 변경 없이 보관했다. 이 문서는 해당 코드의 설명이며 새 모델 수리 실험 보고서가 아니다.

## 실행 흐름과 책임

고정 문제 등록 → 입력 검증 → 오류 분류 → proof body 수정 → 재검증을 반복한다. 예비 통과 뒤에는 전체 파일을 새 프로세스로 최종 검사한다. 최종 증명 오류는 남은 예산 안에서 수리로 돌아가며, 명제 불일치·환경 실패·한도 소진은 사유를 기록하고 중단한다.

| 설계 책임 | 실제 코드 | 역할 |
| --- | --- | --- |
| TaskSpec | [contracts.py](evidence/verification-repair/lean_repair/contracts.py) | 원본·정리명·proof span·prefix/suffix 해시·commit·toolchain·제한 고정 |
| LeanRunner / verifier adapter | [lean.py](evidence/verification-repair/lean_repair/lean.py), [repl.py](evidence/verification-repair/lean_repair/repl.py) | CLI·community REPL 결과를 공통 계약으로 변환 |
| RepairPolicy / model adapter | [model.py](evidence/verification-repair/lean_repair/model.py) | 현재 후보와 실제 오류·이력 전달, JSON diagnosis/proof_body 수신 |
| Controller | [controller.py](evidence/verification-repair/lean_repair/controller.py) | 최초 검사, 기본 최대 3회 수리, 중복 후보·자원 재시도·중단 관리 |
| FinalVerifier | [controller.py](evidence/verification-repair/lean_repair/controller.py) | 최종 전체 파일 재검증; 예비 성공과 최종 수락 분리 |
| Trace / process runner | [runtime.py](evidence/verification-repair/lean_repair/runtime.py) | 후보·명령·stdout/stderr·JSONL·종료 이유와 프로세스 제한 |

원래 [DESIGN 4·5·6](evidence/design.md)의 논리적 책임을 하나의 Python controller와 adapter로 연결한 구현이다. 별도 여러 에이전트가 실행된다는 뜻은 아니다. imports·명제·가정·정의는 고정하고 전체 proof body만 교체한다. 본문 안의 국소 `have`는 허용한다. 각 후보는 별도 파일로 저장하며 원본을 덮어쓰지 않는다.

이미 판정한 동일 후보는 캐시하지만 timeout·environment/process 오류는 확정 proof 판정으로 저장하지 않는다. `infra_retries` 범위의 별도 재시도를 적용한다. 명제·namespace·고정 문맥 불일치는 `statement_mismatch`로 즉시 종료하며 모델에 수리를 요청하지 않는다. 시작 시 설정 오류도 Trace와 result.json으로 보존한다.

## 반환 계약과 실제 진단 수집

[VerificationResult](evidence/verification-repair/lean_repair/contracts.py)는 task/attempt/candidate/environment 식별자, check_kind, status와 process_exit_code, diagnostics, goals, local_context, sorries, backend_proof_status, statement_check, axioms, metrics, elapsed_ms, raw_log_path, detail/failure_kind를 분리한다. `status`는 proof_error·incomplete·candidate_pass·verified·invalid_candidate·statement_mismatch·timeout·environment_error·process_error 등을 구분하고 전체 controller의 `stop_reason`과는 별도로 기록한다.

| 필요한 정보 | 구현 방법 | 관측 한계 |
| --- | --- | --- |
| 오류 위치·범위·원문 | Lean JSON의 pos/endPos/data/raw 보존, 원본 문자 offset·source line 부가 | backend가 제공한 범위만 사용 |
| actual / expected 타입 | diagnostics.py가 지원하는 Lean 타입 오류 메시지에서 `expected_actual_types` 추출 | 모든 오류를 일반 의미 분석하는 것은 아님 |
| 실패 전술 원문 | 진단 복사본에서 Lean InfoTree를 수집하고 오류 위치를 감싸는 가장 안쪽 tactic 선택 | 문법 오류 등으로 InfoTree가 없으면 이유와 null 유지 |
| 현재 goal·local context | native tactic 실행 전 상태를 source 위치에 대응, goal과 지역 가정 분리 | 문자열 추측이나 임의 전술 whitelist로 보충하지 않음 |
| 미완성·sorry | 남은 goals, 명시적 sorry/admit 위치, 전이 공리 sorryAx를 별도 검사 | goals 미수집 null과 실제 빈 목록 []를 구분 |

자세한 구현은 [diagnostics.py](evidence/verification-repair/lean_repair/diagnostics.py)와 [Support.lean](evidence/verification-repair/lean_repair/Support.lean)에 있다. `unsolved goals`만 있으면 incomplete이고 타입·구문·미정의 이름 오류가 함께 있으면 proof_error를 우선한다. 단순히 exit 0이나 goals=[]만으로 verified를 반환하지 않는다.

실제 관측 예시는 [미완성 목표](evidence/verification-repair/runs/open-goals-v2/result.json)와 [InfoTree 오류 피드백](evidence/verification-repair/runs/infotree-feedback-v2/result.json)에 있다. 후자는 `exact h.1`의 실패와 목표 Q·P를 보존한 기록이다. 이 자료의 시연 결과는 LLM이 만든 수리 성공률이 아니다.

## 최종 수락과 REPL

community REPL command/file/tactic 응답을 같은 계약으로 정규화한다. REPL의 종료 코드 0, `proofStatus=Completed`, 빈 goals만으로 원래 선언이 교체됐다고 간주하지 않는다. 예비 통과 뒤에는 수정 proof를 원래 문맥에 조립한 **전체 파일을 새 CLI 프로세스에서 검사**하고 대상 선언의 전이적 공리를 확인한다. sorryAx와 승인하지 않은 공리를 수락하지 않는다.

명제 보존은 정확한 고정 prefix/suffix·편집 범위·정리 식별자 검사에 근거한다. 독립 의미 Comparator는 후속 단계이며, 코드가 임의의 다른 명제와 의미적 동등성을 판정하는 구현은 아니다. 구문 guard는 기존 프로젝트의 tactic/macro를 신뢰하므로 적대적 코드의 OS sandbox를 대신하지 않는다.

## proof token·heartbeat·API 예산

Proof token은 해당 환경의 Lean lexer가 센 proof body 토큰이며 모델 input/output 토큰과 다르다. Heartbeat는 동기 elaboration 전후 `IO.getNumHeartbeats` 차이이고 imports·계측 helper·token 계산을 제외한다. raw_heartbeats와 `raw // 1000` 단위의 heartbeats를 함께 기록한다. 참조본과 후보는 같은 환경에서 측정하고 token/HB 감소율을 각각 계산한다.

OpenRouter adapter는 공개 가격과 모델 context 길이·최대 출력량으로 호출 전 최대 비용을 예약하고, 실제 usage·공급자 비용으로 정산한다. 문제별 원장은 실행 폴더 밖에 누적하며 재실행·동시 실행·중단 후에도 초기화하지 않는다. 실패·timeout·미수신 usage는 0원으로 처리하지 않고 예약을 유지한다. 기본 문제당 USD 3 제한은 이 adapter의 로컬 통제이며 공식 평가 합격이나 공급자 청구의 정확성을 보증하지 않는다.

이 구현의 OpenRouter 연결 코드와 [15문제 실험](../../refactoring/warmup/손지연/verification-repair-experiment.md)의 **실제 구독 CLI 사용**은 구분한다. 원래 구현 시험에는 실제 모델 호출이 없었고, 실험에서는 유료 API로 전환하지 않았다. 구독 사용량을 USD 3 API 실행으로 소급하지 않는다.

## 보존된 검증 결과와 이번 확인

원래 [validation.json](evidence/verification-repair/validation.json)과 [전체 시험 로그](evidence/verification-repair/validation-tests.log)는 2026-10-22 **73개 테스트 통과·skip 0·유료 API 요청 0회**를 기록한다. CLI는 Lean 4.31.0·4.33.0-rc2, 실제 REPL은 v4.31.0 commit `0cc60263319308000bbaa5354427f775fe3dc7d0`이다. 해당 외부 binary나 임시 통합시험 디렉터리를 공유 자료에 새로 포함했다고 주장하지 않는다. 원래 JSON의 과거 절대 경로는 증거로 보존한다.

이번 정리는 원래 코드·시험·증명·로그를 바꾸지 않았다. 새 위치의 CLI 도움말과 모의 adapter·순수 로직 51개 시험을 별도 wrapper로 확인하며, 실제 Lean 통합시험과 새 모델 호출은 수행하지 않는다. 이번 확인은 [공유 정리 검사](evidence/packaging-checks.json)에 원래 73개 시험과 분리해 기록한다.

이 폴더에서 사용할 명령:

```sh
python3.12 evidence/reproduce.py cli --help
python3.12 evidence/reproduce.py unit
```

wrapper는 원래 시험의 `week4.lean_repair` import 이름을 보존하도록 복사본 위치만 연결한다. 원래 package·tests의 코드는 수정하지 않는다. 다른 문제를 실제 검사하려면 준비한 Lean/Lake 환경에서 새 task를 등록해야 하며, 보존 예제 JSON의 과거 절대 경로를 현재 환경으로 오인해서는 안 된다.

기능별 상세 사용법은 [원래 README](evidence/verification-repair/README.md), 실제 예제는 [examples](evidence/verification-repair/examples/), 원래 smoke 기록은 [runs](evidence/verification-repair/runs/)에 있다. 원래 README의 `python3 -m week4.lean_repair` 명령은 이 공유본에서 `python3.12 evidence/reproduce.py cli`로 바꿔 실행할 수 있다. 새로운 검증 출력과 예산 원장은 보존된 evidence와 다른 경로를 사용해야 한다.
