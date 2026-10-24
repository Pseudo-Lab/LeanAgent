# 실험 근거와 재현

`experiment/`는 원래 `week4/experiment`의 코드·설계·데이터·후보·측정·로그 복사본이다. 재생성 가능한 envs·Python/그림 캐시는 제외했다. `runs/20261024T000653+0900/` 아래의 P_A/P별/조건/반복, V_B/P별/오류/조건/반복 구조를 그대로 유지한다. 모든 proof·측정 JSON·원시 로그의 내용과 과거 경로 문자열을 보존한다.

- [원래 설계](experiment/DESIGN.md), [프로토콜](experiment/runs/20261024T000653+0900/protocol.json), [환경 pin](experiment/runs/20261024T000653+0900/environment_manifest.json).
- [P-A / V-B 이력](experiment/runs/20261024T000653+0900/runs/), [V-A fixture](experiment/runs/20261024T000653+0900/V_A/).
- [집계 JSON·CSV](experiment/runs/20261024T000653+0900/analysis/), [후보 호환성](experiment/runs/20261024T000653+0900/compatibility/), [과거 실제 Lean 재검증](experiment/runs/20261024T000653+0900/revalidation/).
- [원본·복사본 검증](packaging/preservation.json), [복사 manifest](packaging/copy-manifest.jsonl), [새 위치에서의 기록 재생](packaging/record-replay.json).

모델·Lean 없이 새 위치에서 기록을 재생하려면 발표자 폴더에서 실행한다.

```sh
python3.12 evidence/packaging/reproduce.py
```

이 wrapper는 보존된 engine/replay의 순수 함수만 읽고 360이력의 요청·상태·best·최종 선택·종료·예산 합계를 재계산한다. 원래 모듈의 초기화나 모델·Lean runner를 실행하지 않는다. 출력은 `packaging/record-replay.json`이고 보존 이력을 덮어쓰지 않는다.

다른 컴퓨터에서 `share/` 안의 복사본만 검사하려면 `packaging/build_share.py --verify-copy`를 사용한다. 원본도 같은 workspace에 있을 때의 `--verify`는 원본 SHA·mtime·inode·파일 목록을 다시 대조한다. 환경 캐시 내부의 Git 자동 갱신은 검사 범위에 포함하지 않으며 해당 경로에 쓰지도 않는다.

원래 실험 실행 스크립트는 당시 checkout·캐시·절대 경로를 전제로 한 **보존 코드**다. 그대로 실행하면 새 출력이나 모델 호출이 생길 수 있으므로 이번 읽기 전용 재현에는 위 wrapper를 사용한다. 새 모델·Lean 실험의 환경 복원과 실행은 이번 공유 정리의 검증 범위 밖이다.
