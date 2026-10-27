# 15문제 통합 P/V 실험

`DESIGN.md`를 기준으로 실행한다. 정상 원본의 리팩터링(P)과 의도적으로 손상한 proof의 복구(V)를 분리한다. 이전 `experiment-v0`, `experiment-v1`의 모델 실행은 이번 결과에 포함하지 않는다.

사용자 승인에 따라 **기존 ChatGPT 구독 인증만 사용**한다. 유료 API/구매 크레딧으로 전환하지 않는다. 정상 proof의 OpenAI Codex/ChatGPT 전송도 승인받았다. USD 비용·USD 3 엄격 준수·달러 기준 곡선·공식 점수는 `null`이다. 실제 호출 수와 입력/출력 token 곡선은 별도로 기록한다. 구독의 포함 사용량을 API 목록 가격으로 환산하지 않는다.

현재 실행 경로는 `LATEST_RUN`에 있다. 상태·중간 보고서는 계속 갱신되며 `complete`를 확인해야 한다.

이번 실행의 [보고서](runs/20261024T000653+0900/REPORT.md), [브라우저용 보고서](runs/20261024T000653+0900/report.html), [측정 상태](runs/20261024T000653+0900/analysis/status.json)에서 결과와 미확정 항목을 확인할 수 있다.

새 독립 실험은 현재 실행의 `completion.json`이 완료를 확인한 뒤 `python3 week4/experiment/bootstrap.py --new-run`으로 시작한다. 실행 중에는 `LATEST_RUN`을 전환하지 않는다. 그 다음 아래 준비·실행 명령을 같은 순서로 적용한다.

```sh
python3 week4/experiment/follow.py
python3 week4/experiment/analyze.py
```

고정된 프로토콜은 `runs/<run_id>/protocol.json`, 전송 승인은 `egress_approval.json`에 있다. 15문제·36개 문제/버전 조합·15개 고정 환경을 대상으로 한다. 기본 환경은 이전에 원본과 캐시가 확인된 핀으로 사전 선택했으며, 나머지는 holdout이다. P-A는 15×4전략×3반복=180개 이력, V-A는 15×6변형=90사례, V-B는 15×2오류범주×2조건×3반복=180개 이력이다.

P-A0는 1회, P-A1~3은 최대 3회 제안한다. V-B는 최대 4회다. 이력당 240,000 soft model token 예약 한도, 모델 300초/호출, Lean 300초/프로세스, 전체 이력 5,400초 한도를 사용한다. quota가 불명확하거나 90% 이상이거나 추가 크레딧 사용 가능 상태면 새 호출을 차단한다. 토큰 예약 초과 등으로 실제 호출 수가 상한보다 작아질 수 있다.

실행·재개 명령(완료 결과와 모델 ledger를 덮어쓰지 않음):

```sh
python3 week4/experiment/prepare.py restore --workers 3
python3 week4/experiment/prepare.py build --workers 2
python3 week4/experiment/tasks.py --workers 3
python3 week4/experiment/validation.py --workers 2
python3 week4/experiment/suite.py P_A --workers 5 --wait-inputs
python3 week4/experiment/suite.py V_B --workers 3 --wait-inputs
python3 week4/experiment/holdout.py --workers 2
python3 week4/experiment/replay.py
python3 week4/experiment/revalidate.py --workers 2
python3 week4/experiment/controls.py
python3 week4/experiment/audit.py
python3 week4/experiment/analyze.py
python3 week4/experiment/figures.py
```

`python3 week4/experiment/finish.py`는 주 실행 완료를 기다린 뒤 holdout → replay/controls → 남은 fresh revalidation → audit/분석/그림을 순서대로 마무리한다. `completion.json`과 `analysis/status.json`의 완료 여부가 최종 기준이다. 새 모델 호출은 하지 않는다. 메모리 사용량이 큰 환경이 있으므로 별도 revalidation worker를 여러 개 중복 실행하기보다는 2~4개로 시작한다.

후속 평가가 모두 끝나면 `python3 week4/experiment/finalize.py`로 전체 문제·조건·반복 및 후보/환경 검사 누락, 저장 proof 해시, 원본 보존을 다시 대조하고 최종 소스 snapshot·보고서를 만든다. coverage가 부족하면 완료로 닫지 않는다. 실행 완료와 비용/토큰 계측의 완전성은 별도 필드로 유지한다.

`prepare.py`는 지정 커밋/toolchain만 복원하며 기존 의존성 핀을 갱신하지 않는다. 준비된 이전 환경의 소스·캐시는 읽어 재사용한다. 새 코드·입력·모델 응답·검증 로그·보고서는 모두 이 디렉터리 안에 있다. 원래 `week4/verification-repair` 패키지는 수정하지 않았다. 명세·문맥·imports·가정은 해시로 고정하고 proof body만 바꾼다.

H 모드에서는 기준 버전 token/HB만으로 best를 선택하고 최종 proof 해시를 먼저 확정한다. 이후 지정된 모든 버전에 동일 proof bytes를 적용한다. P-B는 이력별 동일 후보군에 네 선택 정책을 사후 적용하며 새 모델 호출을 하지 않는다. 일부 환경이 준비/검증 불가이면 호환성·종합점수를 0으로 채우지 않고 미확정으로 둔다.

V-A의 기대 상태는 fixture 정의에서 먼저 작성한다. 실제 패키지가 직접 `sorry`를 `invalid_candidate`로 거절하는 경우 DESIGN의 기대 라벨 `incomplete`와의 차이를 보존한다. 실제 Lean subprocess timeout과 synthetic 정책 테스트는 구분한다.

P10의 최초 오류 입력은 다중 행 괄호 항을 잘못 잘라 문법 경계 거절을 일으켰다. 모델 호출 전에 원문 구조를 유지하고 실제 참조 식별자만 바꾸도록 사전 검증을 보정했다. 최초 기록은 `preflight_rejected/`, 근거는 `fixture_amendments.jsonl`에 보존했다. 두 V-B 조건은 보정된 동일 입력을 사용한다.

V-C `replay.py`는 저장된 모델·검증·예산 이벤트로 요청/전이/best/선택/종료를 재계산하며 새 Lean·모델 호출을 하지 않는다. `revalidate.py`는 별도로 실제 Lean을 다시 실행하며 상태·해시·공리·진단·token·HB·버전별 차이를 항목별로 기록한다. 프로세스 제어 테스트를 모델 제공자의 오류율이나 검증기의 일반적 안전성 증명으로 해석하지 않는다.

각 이력은 파일 잠금으로 중복 실행을 차단한다. 중단된 모델 호출의 사용량이 확인되지 않으면 새 호출을 하지 않는다. 해당 ledger를 지우고 처음부터 실행하면 비용을 숨기게 되므로 그렇게 재개하지 않는다. 원본 package 해시 및 작성 코드 해시·구현 정리 내역은 manifest와 `implementation_notes.json`에 저장한다.

주요 산출물은 `REPORT.md`, `report.html`, `analysis/summary.json`, `selection_comparison.json`, `budget_curve.json`, `usd_budget_checkpoints.json`, `feedback_comparison.json`, `validation_comparison.json`, `record_replay.json`, `lean_revalidation.json`, `control_checks.json`이다. 실행 전/중에는 아직 없는 파일이 있을 수 있다.

최종 정리에서는 `analysis/candidate_lineage.json`과 `derived/runs/.../candidate_diffs/`에 부모 proof 해시와 수정 diff를 내보낸다. 실제 요청의 입력 bytes와 대조한 사후 파생 자료이며 원래 모델 이력은 수정하지 않는다. `reproducibility/`에는 최종 분석 소스와 dependency 버전을, 모델 이력의 `effective_runner.json`에는 실제 당시 worker가 사용한 engine 버전을 보존한다.
