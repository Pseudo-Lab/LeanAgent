# Week 4 실험 근거와 재현

2026-10-24 실행 `20261024T000653+0900`의 보존 기록입니다. 로컬 `share/` 원본을 유지한 채 Git에 올릴 근거를 선별했습니다. 과거 경로 문자열과 포함된 코드·증명·측정·로그의 바이트는 보존합니다.

- 실험 설계: [DESIGN.md](experiment/DESIGN.md).
- 고정 조건: [protocol.json](experiment/runs/20261024T000653+0900/protocol.json) · [환경 pin](experiment/runs/20261024T000653+0900/environment_manifest.json).
- 결과: [집계 JSON·CSV](experiment/runs/20261024T000653+0900/analysis/) · [기록 재생 결과](packaging/record-replay.json).
- 과거 실제 Lean 재검증: [1,213건 집계 원문(gzip)](experiment/runs/20261024T000653+0900/analysis/lean_revalidation.json.gz). 압축 해제 후 JSON 바이트가 원본과 같습니다.
- 360개 이력: [보고서의 대표 7개 사례](../verification-repair-experiment.md)의 기록은 직접 탐색할 수 있습니다. 나머지 353개 이력과 입력·fixture·호환성·기준 검증 기록은 [records.tar.gz](experiment/records.tar.gz)에 보관합니다.
- 포함·생략 범위와 SHA-256: [provenance.json](packaging/provenance.json) · [포함 파일 목록](packaging/included-files.json) · [전체 로컬 원본 목록(gzip)](packaging/copy-manifest.jsonl.gz).
- 재사용 검증·수리 구현: [구현 근거 안내](../../../../verifier-guided-agent/손지연/evidence/README.md).

모든 이력의 config·events·result·ledger·manifest, 모델 요청·응답, 후보 proof/metadata와 존재하는 최종 선택 proof를 보관합니다. 거대한 InfoTree 출력, 중복 validation 소스, Lean 컴파일 산출물, 검증 subprocess의 원시 출력 등은 PR에서 생략했습니다. 기존 원본은 `share/`에 남아 있으며 전체 목록에서 생략 파일의 경로·해시·크기를 확인할 수 있습니다. Git의 근거 묶음만으로 원시 출력 전체를 감사하거나 새 Lean 실험을 재현할 수 있다고 주장하지 않습니다.

보존 코드·CSV·로그·SVG에는 원래 줄바꿈과 공백이 있습니다. 근거 폴더의 `.gitattributes`로 해당 원본의 줄바꿈 정규화를 막고 공백 검사를 제외합니다. 공유 문서와 새 재생·검사 스크립트에는 일반 검사를 적용합니다.

## 저장 기록 재생

Python 3.11 이상으로 발표자 폴더에서 실행합니다. 모델·Lean·네트워크를 호출하지 않습니다.

```sh
python3.12 evidence/packaging/reproduce.py --output /tmp/sonjiyeon-week4-replay.json
python3.12 evidence/packaging/verify.py
```

첫 명령은 압축된 기록을 임시 폴더에 안전하게 풀고 대표 7개 사례를 합쳐 360개 이력의 요청·상태·best·최종 선택·종료·예산을 재계산합니다. 저장된 순수 함수만 읽고 과거 runner의 초기화는 실행하지 않습니다. 두 번째 명령은 포함 파일과 압축 내부의 SHA-256를 원본 목록과 대조합니다.

`experiment/`의 실행·분석 스크립트와 README는 당시 checkout·캐시·절대 경로를 전제로 한 보존 코드입니다. 현재 위치의 기록 재생에는 위 명령을 사용합니다. 새 모델·Lean 실행과 환경 복원은 이번 문서 정리에서 수행하지 않았습니다.
