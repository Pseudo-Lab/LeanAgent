# Warmup 15 · 실험 코드와 실행 방법

2026-10-26에 시험한 15문제의 편집 후보와 검증 기록이다. 출발 증명은 `starting-selection.json`, 작성자와 출처는 `starting-manifest.json`에 있다. 추가 점수는 출발 증명과의 차이다.

이 README가 있는 `docs/research/refactoring/warmup/정소미/evidence/warmup15-20261026/`에서 명령을 실행한다. Python 3.10 이상, Git, Lean 버전 관리 도구 Elan이 필요하다.

## 실행 흐름

`후보 생성 → 전체 파일 검사 → 오류 수정 → 3회 측정 → 버전 확인 → 선택`

`experiment.py`는 기존 검사기를 호출한다. `generators/`에는 이번 15문제에 시험한 편집이 들어 있다. 고정된 `starting-selection.json`에서 후보를 생성한 뒤 Lean으로 검증한다. 이 명령은 모델 API를 호출하지 않는다.

```sh
python3 experiment.py generate --output /tmp/warmup15-candidates
```

다른 출력 폴더에서 원본과 출발 후보를 함께 재측정한다. 아래 예시는 P09의 후보 하나를 측정한다. `--candidate`를 생략하면 해당 문제에서 생성한 후보를 모두 실행한다.

```sh
python3 experiment.py verify \
  --arena /path/to/LeanAgent-LeanRefactorArena \
  --project /path/to/pinned-cslib \
  --problem 9 --version v4.32.0 \
  --candidates /tmp/warmup15-candidates/candidates.json \
  --candidate 06-expected-relation-witnesses --runs 3 \
  --output /tmp/warmup15-p09-verification
```

준비된 라이브러리 저장소는 `benchmark.jsonl`의 `version_info`에 있는 정확한 커밋과 Lean 버전이어야 한다. 의존성 빌드를 마친 깨끗한 체크아웃을 명시적으로 넘긴다. 실행 도구가 저장소나 패키지를 수정하지 않으며, 전후에 소스·의존성 커밋과 변경 여부를 검사한다. 환경 준비 실패를 증명 실패나 0점으로 바꾸지 않는다.

검사기 버전은 다음 두 커밋으로 고정했다. `b5ad8ace25c8f1eed712b662f9a0d092562e3ebc`는 전체 문맥과 P12 별도 경로를 연결하는 Arena 실행 도구의 버전이고, `c18ec56682462847e2f4d8b6d60aa79ec071a10b`는 공통 토큰·HB 평가기 자체의 버전이다. `verifier-identity.json`이 실행 도구 파일의 해시를 기록한다. 당시 실행 스크립트와 원자료도 함께 저장했다. 통합 명령의 재실행 결과는 별도 기록이다.

P09 v4.32.0 환경을 새로 마련하는 예시는 다음과 같다. 출력 경로는 비어 있어야 한다. 다른 버전은 `benchmark.jsonl`의 해당 행에 있는 커밋으로 별도 체크아웃을 만들어 같은 검증 명령을 반복한다.

```sh
git clone https://github.com/Pseudo-Lab/LeanAgent-LeanRefactorArena.git /tmp/warmup-arena
git -C /tmp/warmup-arena checkout b5ad8ace25c8f1eed712b662f9a0d092562e3ebc
git clone https://github.com/leanprover/cslib.git /tmp/warmup-cslib
git -C /tmp/warmup-cslib checkout 197a7be621263b84c67ca4f803f69205b36d06df
(cd /tmp/warmup-cslib && elan toolchain install leanprover/lean4:v4.32.0 && lake exe cache get && lake build +Cslib.Languages.CCS.BehaviouralTheory:olean)
```

위 `verify` 명령의 `--arena`와 `--project`에 각각 `/tmp/warmup-arena`, `/tmp/warmup-cslib`를 지정한다. 라이브러리 구축에는 다운로드 시간과 디스크 공간이 필요하며, 모델 호출 예산과는 별도다.

HB(heartbeat)는 Lean 내부 계산량 카운터이며 벽시계 실행 시간이 아니다. 토큰은 고정 구문 계산기로 센 증명 본문 토큰이다.

`verify` 결과는 지정한 출력 폴더의 `result.json`과 후보별 Lean 원문·로그다. `controlsValid`와 개별 후보의 `valid`, 3회 측정값을 먼저 읽는다. 지정 버전마다 별도로 확인한 뒤 점수식을 적용한다. 통합 명령의 P09 실행 기록은 `raw/replay-verify-final-p09.tar.gz`에 있다. 이 1회 실행은 명령 동작을 확인한 기록이며, 성능 선택에는 별도 3회 측정값을 썼다. 선택 결과는 `selection.json`, 증명은 `selected/`에 있다.

## 통과와 선택

- 고정 명제, 원문 전체 문맥과 후속 선언을 유지한다. 허용 공리는 `propext`, `Classical.choice`, `Quot.sound`다.
- 공통 평가기는 HB 원시값을 1,000으로 나눈 내림값을 기록한다. 선택 전 원본·출발·새 후보를 같은 환경에서 각각 새 프로세스 3회 측정하고 중앙값을 쓴다.
- 개선 점수는 `50 × (1 − 후보 토큰/원본 토큰) + 50 × (1 − 후보 HB/원본 HB)`다. 출발 후보 대비 추가 점수는 두 후보 점수의 차이다. 분모는 같은 실행의 원본이다.
- 토큰과 HB의 감소율 평균으로 선택했다. P01·P05·P08·P10은 한 지표가 늘고 다른 지표가 줄었다. 두 지표가 함께 줄어든 문제는 P07·P11·P12·P14이고, P09는 토큰 수가 같다.
- P12는 유효한 `#(...)` 유한 기수 표기를 허용하는 기존 Somi full-source v2 경로로 검사한다. 명제를 변경하지 않으며, 공통 평가기와 계측 경로가 달라 **공통 14문제 평균에서 제외**한다.
- `status=completed`는 실행 종료를 뜻한다. 후보 통과 여부는 `valid`, 반복 횟수와 지정 버전 결과에 기록된다.

모델 호출 비용은 계측하지 않아 문제당 $3 조건 충족 여부는 확인하지 못했다. 측정값은 로컬·CI 결과이며 공식 Arena 점수는 아니다. 실험 범위는 이 15문제의 편집 후보다.

## 보존된 결과 다시 집계

`raw/*.tar.gz`에는 실행별 JSON, Lean 원문, 원시 로그와 당시 실행 스크립트가 들어 있다. 파일별 SHA와 압축 묶음 SHA는 `archive-manifest.json`에서 확인한다. 원자료의 당시 컴퓨터 경로는 출처 정보이며 새 실행의 입력 경로로 쓰지 않는다. 변경하지 않은 출발 후보의 이전 검증은 `prior-evidence/`에 별도로 보존했다. `p11-local-repair` 묶음은 로컬 출발 증명 검사에서 시간 제한에 걸려 중단한 환경 진단이며, 새 후보의 실패 횟수나 성능 선택에 넣지 않았다.

압축 묶음을 모두 같은 빈 폴더 `/tmp/warmup15-runs`에 풀면 `p01-p06/`, `p07-p09/`, `p10-p15/`, `ci-…/` 구조가 생긴다. 다음 명령은 저장된 검증 집계로 15개 선택을 재현한다. 모든 생성 후보의 실제 시도 기록이 있어야 하며, 더 좋은 후보의 지정 버전이 대기 중이면 중단한다.

```sh
python3 select_results.py --runs-dir /tmp/warmup15-runs --output /tmp/warmup15-selection
```

`select_results.py`는 저장된 검증 결과를 집계한다. 새 후보의 Lean 검사는 `experiment.py verify`로 실행한다. 원격 자료의 원문·로그 해시, 측정 횟수와 문맥은 `summarize_remote.py`, P01–P06의 전체 소스 재구성은 `audit_native.py`로 추가 확인했다.

원격 실행 기록: [P10–P15 대표 버전](https://github.com/Pseudo-Lab/LeanAgent-LeanRefactorArena/actions/runs/40243352796), [P12 수리·3개 버전](https://github.com/Pseudo-Lab/LeanAgent-LeanRefactorArena/actions/runs/40243802524), [P14 추가 버전](https://github.com/Pseudo-Lab/LeanAgent-LeanRefactorArena/actions/runs/40244093308), [P10·P11 최종 버전 검사](https://github.com/Pseudo-Lab/LeanAgent-LeanRefactorArena/actions/runs/40271664675). 실패한 후보도 실행 기록에 포함돼 있다. 전체 작업이 실패로 표시된 경우에도 개별 결과에서 원본·출발·선택 후보의 통과 여부를 볼 수 있다.
