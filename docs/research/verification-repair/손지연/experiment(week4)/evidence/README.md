# 검증·수리 연구의 근거와 재현

[통합 보고서](../report.md) · [통합 측정 요약](../metrics.json)

## 구현과 실험의 연결

| 자료 | 경로 | 범위 |
| --- | --- | --- |
| 검증·수리 구현 | [implementation](implementation/README.md) | 설계, lean_repair package, CLI/REPL 예제, 시험, 2026-10-22 검증 기록 |
| 15문제 실험 | [experiment](experiment/README.md) | 2026-10-24 실험 harness·데이터·프로토콜·후보·원시 로그·집계·그림 |
| 보존·재생 | [packaging](packaging/) | 원본 보존 manifest·검사 기록과 모델/Lean 없이 실행하는 재생 wrapper |

구현은 결과 계약과 controller의 책임을 설명하고, 실험 harness는 실제 구독 모델 호출로 판정·수리·선택을 비교한다. OpenRouter adapter 시험을 구독 실험의 API 비용 측정으로 취급하지 않는다.

## 구현 확인

Python 3.11 이상을 사용한다. 저장소 루트에서 현재 자료 디렉터리로 이동한 뒤 실행한다.

```sh
cd 'docs/research/verification-repair/손지연/experiment(week4)'
python3 evidence/implementation/reproduce.py cli --help
python3 evidence/implementation/reproduce.py unit
```

namespace wrapper는 기존 `week4.lean_repair` import를 보존한다. unit은 controller·diagnostics·mock HTTP/예산·task·process의 51개 시험이며, 과거 실제 Lean/REPL 포함 73개 시험과 분리한다. [원래 validation](implementation/verification-repair/validation.json)과 [기존 공유 검사](implementation/packaging-checks.json)를 참고한다.

## 실험 근거와 기록 재생

- [설계](experiment/DESIGN.md), [프로토콜](experiment/runs/20261024T000653+0900/protocol.json), [환경 manifest](experiment/runs/20261024T000653+0900/environment_manifest.json).
- [P-A·V-B 이력](experiment/runs/20261024T000653+0900/runs/), [V-A fixture](experiment/runs/20261024T000653+0900/V_A/).
- [집계 JSON·CSV](experiment/runs/20261024T000653+0900/analysis/), [후보 호환성](experiment/runs/20261024T000653+0900/compatibility/), [과거 fresh Lean 재검증](experiment/runs/20261024T000653+0900/revalidation/).
- [기존 보존 검사](packaging/preservation.json), [복사 manifest](packaging/copy-manifest.jsonl), [기존 기록 재생 결과](packaging/record-replay.json).

같은 자료 디렉터리(`docs/research/verification-repair/손지연/experiment(week4)/`)에서 다음을 실행한다.

```sh
python3 evidence/packaging/reproduce.py --output /tmp/verification-repair-record-replay.json
```

보존된 engine/replay의 순수 함수만 읽어 360이력의 요청·상태·best·최종 선택·종료·예산 합계를 재계산한다. 원래 모듈 초기화, 모델·Lean·네트워크 호출은 수행하지 않는다. 출력 경로를 생략하면 `packaging/record-replay.json`을 갱신한다.

## 보존 범위

proof·측정 JSON·소스·원시 로그와 당시 절대 경로 문자열을 보존했다. 환경·Python·그림 캐시의 기존 제외 범위는 이전 보존 기록을 따른다. 구현·실험 내부의 역사적 경로는 당시 실행의 증거이므로 현재 경로로 치환하지 않았다.

`packaging/`의 기존 구조 검사·공유본 생성 도구는 병합 전 디렉터리 배치를 전제로 한다. 현재 재생에는 위 `reproduce.py`를 사용한다. 원래 실험 실행 스크립트는 당시 checkout·캐시·절대 경로를 전제로 하며, 새 실행에는 별도의 환경 복원이 필요하다. 새로운 검증 출력과 예산 원장은 보존된 evidence와 다른 경로를 사용한다.

[병합 전 공유 문서](packaging/source-documents/README.md)는 출처 확인용으로 보관했다. 현재 읽기·탐색 경로는 통합 보고서와 이 안내를 따른다.
