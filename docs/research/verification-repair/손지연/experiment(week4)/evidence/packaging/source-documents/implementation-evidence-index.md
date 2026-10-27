# 구현 근거와 재현

`verification-repair/`는 원래 구현의 package·examples·tests·runs·validation을 그대로 보관한다. `design.md`는 원래 설계 4·5·6번을 포함한 문서 사본이다. Python 캐시는 제외하며 원본 소스와 로그는 수정하지 않는다.

발표자 폴더에서 다음을 실행한다. Python 3.11 이상이 필요하다.

```sh
python3.12 evidence/reproduce.py cli --help
python3.12 evidence/reproduce.py unit
```

namespace wrapper로 과거 `week4.lean_repair` import를 연결한다. unit은 controller·diagnostics·mock HTTP/예산·task·process 시험 51개다. 실제 Lean/REPL 통합시험은 새로 실행하지 않는다. 보존 예제의 환경 경로는 과거 기록이므로 실제 새 검사에는 준비한 프로젝트로 task를 새로 등록한다.

원래 2026-10-22의 73개 시험과 이번 검사는 [원래 validation](verification-repair/validation.json), [공유 정리 검사](packaging-checks.json)로 분리한다. 구현의 API adapter 코드 존재와 실제 모델 수리 검증을 구분한다. 전체 proof·측정·로그 SHA-256은 Warm-up evidence의 [공통 보존 검사](../../../refactoring/warmup/손지연/evidence/packaging/preservation.json)에 포함한다.
