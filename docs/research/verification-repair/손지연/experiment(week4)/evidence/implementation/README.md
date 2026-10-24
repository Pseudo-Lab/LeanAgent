# 검증·수리 구현 근거

[통합 보고서의 구현 설명](../../report.md#implementation) · [공통 재현 안내](../README.md)

- [설계](design.md), [설계 출처](design-source.json).
- [보존된 package·사용법](verification-repair/README.md), [소스](verification-repair/lean_repair/), [예제](verification-repair/examples/), [시험](verification-repair/tests/).
- [원래 73개 시험 결과](verification-repair/validation.json), [전체 시험 로그](verification-repair/validation-tests.log), [smoke 실행 기록](verification-repair/runs/).
- [기존 공유 검사](packaging-checks.json), [unit 로그](packaging-unit.log), [공통 보존 기록](../packaging/preservation.json).

저장소 루트에서 현재 자료 디렉터리로 이동한 뒤 실행한다.

```sh
cd 'docs/research/verification-repair/손지연/experiment(week4)'
python3 evidence/implementation/reproduce.py cli --help
python3 evidence/implementation/reproduce.py unit
```

원래 package·tests·로그는 보존했다. namespace wrapper가 과거 `week4.lean_repair` import를 연결한다. 보존 예제의 절대 환경 경로는 당시 실행 기록이며, 실제 새 검사에는 준비한 Lean/Lake 프로젝트로 task를 등록한다.
