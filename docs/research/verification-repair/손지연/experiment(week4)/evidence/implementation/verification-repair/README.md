# 재사용 가능한 Lean 검증·수리 루프

`week3/p7_auto_repair`의 실행 흐름을 한 정리 단위로 일반화했다. Python 3.11+ 표준 라이브러리와 이미 준비된 Lean/Lake 프로젝트를 사용한다. 프로세스 그룹·원장 잠금·API deadline에는 macOS/Linux의 POSIX 기능을 사용한다. P7 전용 이름·타입·전술 목록에 의존하지 않는다. 원본 파일은 수정하지 않고 매번 새 출력 디렉터리에 후보와 검증 근거를 저장한다.

## 바로 실행

레포 루트에서 다음 명령은 **모델/API 호출 없이** 다른 두 정리를 실제 Lean으로 검사한다. 예제 프로젝트는 Lean `v4.33.0-rc2`를 사용한다.

```bash
python3 -m week4.lean_repair check --task week4/examples/swap.json \
  --proof-body week4/examples/swap_body.txt --output week4/runs/swap-check
python3 -m week4.lean_repair check --task week4/examples/nat.json \
  --proof-body week4/examples/nat_body.txt --output week4/runs/nat-check
```

`--proof-body`를 생략하면 설정에 고정된 오류본을 검사한다. 오류본이면 실패 진단을 기록하고 종료하며, `check`는 모델을 호출하지 않는다. `examples/p7.json`은 기존 P7 오류본을 동일한 인터페이스로 읽는 설정이다.

## 다른 문제 등록

한 task는 기존 정리 하나와 해당 정리의 전체 `by` 증명 본문을 대상으로 한다. 먼저 프로젝트 의존성을 준비한 다음 설정을 생성한다.

```bash
python3 -m week4.lean_repair init \
  --source path/to/Problem.lean --project path/to/lake-project \
  --target MyNamespace.my_theorem \
  --declaration-marker 'theorem my_theorem' \
  --body-start-marker ':= by' \
  --body-end-marker 'end MyNamespace' \
  --output week4/my_task.json
```

`declaration-marker`는 속성·`private`·`omit … in`이 있으면 그것까지 포함한 **전체 명령의 시작**이어야 한다. `body-end-marker`는 증명 뒤 고정 문맥의 시작이며 파일 끝까지 증명이 이어지면 생략한다. `init`은 경계를 Unicode 문자 offset과 원본 SHA256으로 고정한다. 선언 시작·본문 시작·본문 끝이 올바른지 생성된 `span`을 확인한다. 같은 파일에서 마커가 모호하거나 복잡한 선언을 쓰면 이 세 offset을 직접 지정할 수 있다. 본문 뒤 명령을 분리하는 줄바꿈은 고정 suffix에 남긴다.

환경의 commit, toolchain, manifest hash도 고정한다. 감사할 `target`은 편집 span의 정리명·namespace와 일치해야 한다. Git 의존성은 lock revision을 확인하며 실행 중 tracked diff 변화를 감시한다. 다른 checkout으로 옮겼으면 의도한 환경에서 설정을 다시 생성한다. 여러 Lean 버전을 평가하려면 버전별 task를 따로 만든다.

정상 참조 파일이 있으면 `--reference path/to/Reference.lean`을 추가한다. 참조본은 증명 본문 외의 prefix/suffix가 오류본과 정확히 같아야 한다. 참조본은 평가기에서만 읽으며 모델에 전달하지 않는다. 참조본이 없으면 후보의 절대 측정값은 기록하고 감소율은 계산하지 않는다.

모델 수리를 실행하려면 설정의 `model.model`을 실제 **유료 OpenRouter model ID**로 바꾸고 `OPENROUTER_API_KEY` 환경변수를 준비한다. 인증 값은 설정·로그에 저장하지 않는다.

```bash
python3 -m week4.lean_repair run --task week4/my_task.json \
  --output week4/runs/my-task-01
```

이 명령은 실제 과금 가능한 호출을 수행한다. 이 작업을 검증할 때는 모델/API 호출을 하지 않았다.

## CLI / community REPL backend 선택

기본 backend는 `cli`다. 프로젝트와 **같은 Lean 버전으로 빌드한** [community REPL](https://github.com/leanprover-community/repl)이 있으면 설정에 다음을 추가한다. `command`는 shell 문자열이 아닌 argv 배열이며 실행 파일은 절대경로를 권장한다.

```json
"backend": {
  "kind": "repl",
  "command": ["/absolute/path/to/repl/.lake/build/bin/repl"],
  "mode": "file"
}
```

`mode`는 전체 파일을 전달하는 `file` 또는 전체 코드를 전달하는 `command`다. CLI에서도 `--backend repl --repl-command '["/absolute/path/to/repl"]'`로 지정할 수 있다. 다른 버전의 REPL이나 실행할 수 없는 binary는 환경 오류로 종료한다. `ReplClient`는 별도 command/file/tactic 요청을 같은 `VerificationResult`로 변환하며 원시 요청·응답을 보존한다.

REPL의 process exit 0·빈 `goals`·`proofStatus="Completed"`만으로 최종 성공 처리하지 않는다. 후보의 범위·토큰·heartbeat·공리는 CLI 검사도 함께 거치고, **최종 수락은 언제나 수정된 전체 파일을 새 CLI 프로세스에서 다시 검사**한다. REPL tactic 성공이 원래 environment의 선언을 자동 교체한 것으로 간주하지 않는다. REPL에서 직접 받은 `backend_proof_status`와 goal/sorry 정보를 반환하며, CLI가 제공하지 않은 backend 상태는 `null`로 남긴다.

## DESIGN.md 4번 반영

| 책임 | 구현 |
| --- | --- |
| TaskSpec | `contracts.py`: 원본·정리·편집 span·환경 pin·제한 고정 |
| LeanRunner / verifier adapter | `lean.py`, `repl.py`, `runtime.py`: CLI/REPL, 실제 진단, 자원 측정, 공통 `VerificationResult` |
| RepairPolicy / model adapter | `model.py`: 현재 후보·실제 피드백을 OpenRouter로 전달하고 `diagnosis/proof_body` 수신 |
| Controller | `controller.py`: 최초 검증, 최대 3회 수리, 중복 제외, 자원 실패의 별도 제한 재시도 |
| FinalVerifier | `controller.py`: 예비 통과 뒤 별도 전체 파일 재검증; 증명 오류이면 예산 안에서 수리로 복귀 |
| Trace | `runtime.py`: `trace.jsonl`, 후보 원문·명령·stdout/stderr·JSON 결과 |

imports·정리문·가정·정의는 고정된 prefix/suffix로 보존한다. 모델은 전체 proof body만 교체하며 그 안의 `have`는 허용한다. Lean backend를 바꿀 때 `Verifier` protocol과 `VerificationResult`를 유지하면 controller/model adapter를 재사용할 수 있다.

이미 확정된 후보만 cache한다. timeout/environment/process 오류는 증명 판정으로 cache하지 않고 `infra_retries`만큼 재시도한 뒤 별도 사유로 종료한다. Lean·모델·준비·전체 task의 wall-clock 제한을 구분한다. 일반 linter warning은 별도 진단으로 남기며 미완성 증명 판정과 혼동하지 않는다.

원래 정리명·namespace·명제·가정·고정 문맥의 불일치는 **`statement_mismatch` / `statement_check="mismatch"`**로 반환하고 즉시 종료한다. 예비 검사·최종 검사·cache·환경 준비 중 어느 단계에서 발견돼도 모델을 다시 호출하지 않는다. 본문 안의 구문·정책 오류인 `invalid_candidate`와 구분한다. `init`이 고정 prefix/suffix hash도 기록하므로 설정을 다시 읽을 때도 문맥 변경을 판별할 수 있다.

`check`/`run`은 설정을 읽기 전부터 Trace를 만들고, 잘못된 JSON·입력 파일 부재·정리명 불일치 등도 `result.json`과 종료 이벤트에 기록한다. `init` 등록 단계의 기록은 설정 파일 옆 `<설정파일>.registration.<시각>/`에 남는다. 예산 원장을 아직 읽지 못한 시작 실패에서는 `api_budget=null`, `api_requests_this_run=0`이다. 누적 비용을 확인하지 못한 상태를 0원으로 표시하지 않는다.

## 토큰·heartbeat·API 예산

Arena 공식 소스의 [규칙 snapshot](https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena/blob/8fdaaaa25b993ae8d894e9bb756c3ae222b58507/app.py)을 2026-10-22에 확인했다. closed track은 **문제당 공개 정가 US$3**, 재시도·폐기 후보를 포함한 **모든 모델 호출**, **OpenRouter 사용**을 요구한다. Proof token/heartbeat 감소율은 평가 축이며 둘 다 감소해야 한다는 하드 조건은 아니다.

| 항목 | 측정·제한 |
| --- | --- |
| `metrics.proof_tokens` | 프로젝트 parser 환경에서 Lean lexer가 센 **증명 본문** 토큰. `by`·국소 보조증명 포함, 공백·일반 주석 제외. 모델 tokenizer와 다름 |
| `metrics.raw_heartbeats` | 대상 선언의 동기 elaboration 전후 `IO.getNumHeartbeats` 차이. import·계측 helper·토큰 계산 제외 |
| `metrics.heartbeats` | `raw_heartbeats // 1000`. `maxHeartbeats`와 같은 단위. 참조와 후보를 같은 환경·범위로 계측 |
| `limits.proof_tokens` | 선택적인 proof 크기 상한. 없으면 측정만 함 |
| `limits.max_heartbeats` | Lean 작업량 기본 상한 200000. 모델의 `set_option` 변경 금지. 원본의 옵션 영향도 실제 측정값으로 다시 확인 |
| `limits.heartbeats` | 선택적인 측정 heartbeat 상한. 기본은 `max_heartbeats`와 동일 |
| `limits.model_tokens` | 선택적인 누적 모델 input+output token 예산. reasoning은 completion의 세부값이므로 중복 합산하지 않음 |
| `limits.api_usd` | 문제당 비용 상한, 기본 `3`. 이 구현의 closed-track 설정은 3을 초과할 수 없음 |

참조본이 있으면 token/heartbeat 감소율을 각각 기록한다. 계측용 파일은 `Elab.async=false`로 실행하며, 최종 수락은 별도로 컴파일한 비계측 파일과 대상 정리의 전이적 공리에 근거한다. `sorryAx`와 미승인 공리는 수락하지 않는다.

OpenRouter의 공개 model catalog에서 가격을 읽고 **호출 전에 최대 비용을 예약**한다. 입력은 모델 전체 context 길이, 출력은 `max_output_tokens`로 보수적으로 예약하므로 작은 prompt라도 큰 context의 고가 모델은 호출 전에 거절될 수 있다. provider 가격 상한과 출력 token 한도를 요청에 함께 전달한다. 모델·가격·provider·실제 usage·공급자가 보고한 cost를 호출별 기록으로 남긴다.

정산은 cache 할인 전 input 정가와 completion 정가를 사용하고 공급자가 보고한 cost가 더 크면 큰 값을 반영한다. [OpenRouter usage 규약](https://openrouter.ai/docs/cookbook/administration/usage-accounting)에 따른 input/output token 수를 사용한다. 실패·timeout·usage/cost 누락은 0원으로 처리하지 않고 예약을 유지하고 중단한다. 예산은 공급자가 돌려주는 사용량·공개 가격에 근거한 로컬 통제이며 공급자의 청구 오류를 되돌리는 결제 기능은 아니다.

원장은 `week4/budgets/<task_id의 hash>.json`에 **실행 디렉터리와 별도로 누적**된다. 같은 문제의 재실행에서도 호출·비용을 초기화하지 않으며 동시 실행을 잠근다. 프로세스 중단 뒤 미확정 예약이 남아도 다음 실행을 차단한다. 동일 문제는 동일 `task_id`로 관리하고 원장과 호출 근거를 함께 보존한다. 실제 과금 내역을 확인하지 않은 채 원장을 삭제해 재시도하지 않는다.

```bash
python3 -m week4.lean_repair report week4/runs/*/result.json
```

`report`는 같은 문제 원장의 누적 snapshot을 중복 합산하지 않고 문제별 비용과 합계·평균·최댓값을 표시한다. 미확정 예약도 포함하므로 `committed_usd`는 실제 청구액이 확정되지 않은 경우 상한 예약을 포함한다. 시작 실패로 누적 원장을 읽지 못한 문제는 비용을 `null`로 표시하고, 확인 가능한 금액은 `known_total_usd`로 따로 제공한다.

## 진단·산출물

`diagnostics`는 Lean JSON의 위치·범위·원문을 보존하고, 해당 형식의 타입 오류에서는 expected/actual을 추출한다. CLI는 별도 진단 복사본의 **Lean InfoTree**에서 오류 위치를 감싸는 가장 안쪽 tactic과 실행 전 goal/context를 읽는다. 전술명 whitelist나 줄 단위 `trace_state` 삽입에 의존하지 않으며 bullet·`case`·여러 줄·중첩 전술도 다룬다. 원본 좌표·UTF-8 byte 범위·실패한 tactic 원문을 기록한다. 문법 오류 등으로 native 정보가 생성되지 않은 경우에는 `null`과 확보하지 못한 이유를 남긴다.

`unsolved goals`만 있으면 **`incomplete`**, 타입/구문/알 수 없는 이름 오류가 함께 있으면 **`proof_error`**다. 실제 남은 목표와 지역 가정도 분리해서 반환한다. 명시적인 `sorry`/`admit`은 구문 위치를 기록하고, 다른 lemma를 통한 미완성은 전이적 `sorryAx` 의존으로 따로 표시한다. 목표가 미수집이면 `null`, backend가 실제 빈 목록을 반환했을 때만 `[]`다.

각 실행에는 다음이 남는다.

- `task.json`, `environment.json`: 입력 pin과 환경 snapshot.
- `lean/`: guard·전체 파일 검사·계측·문맥 진단별 후보와 실행 원문.
- `model/`: 인증을 제외한 요청·응답·가격·usage·오류.
- `trace.jsonl`, `result.json`: 전체 흐름, 공통 검증 결과, 종료 사유와 예산.
- `successful.lean`: 최종 검증을 통과한 원본 문맥의 후보 파일.

이 도구는 신뢰하는 로컬 프로젝트의 한 증명을 수리하는 runner다. Parse-only guard는 명령 삽입·일부 실행 구문을 거절하지만 프로젝트의 기존 tactic/macro는 신뢰한다. 고정 문맥과 공리 검사는 독립적인 의미 비교기나 적대적 코드 sandbox를 대신하지 않는다. Token/heartbeat는 **로컬 측정값**이고 Arena worker의 공식 점수나 여러 버전 호환율은 아니다.

## 검증

```bash
python3 -m unittest discover -s week4/tests -v
```

Controller·원장·HTTP 오류는 모의 adapter로 검사하고, Lean 통합 시험은 설치된 고정 toolchain에서 서로 다른 정리를 실제로 검사한다. 실제 OpenRouter 모델 수리 성능은 이 시험 결과에 포함하지 않는다.

검증 결과와 실제 실행 환경은 [전체 시험 로그](validation-tests.log)와 [측정·검증 목차](validation.json)에 기록한다. REPL 실검증을 재실행하려면 `LEAN_REPAIR_REPL_COMMAND`에 matching binary의 JSON argv, `LEAN_REPAIR_REPL_TOOLCHAIN`에 해당 toolchain을 지정한다. binary가 없는 환경에서는 REPL 통합 시험만 skip하며, 프로토콜 변환 시험은 실행한다.

2026-10-22 후속 검증에서 **73개 테스트 모두 통과**했다. CLI는 Lean 4.31.0·4.33.0-rc2, 실제 REPL은 공식 `v4.31.0`의 commit `0cc60263319308000bbaa5354427f775fe3dc7d0`으로 검사했다. 이 실행에서는 REPL 통합 시험도 skip하지 않았으며, 유료 모델/API 호출은 0회다.
