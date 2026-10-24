# 손지연 Verifier-guided Agent 검증·수리 구현

공유 정리일: 2026-10-24. 공유 모임: 2026-10-25 Week 4. 구현 검증 기록일: 2026-10-22. `week4/verification-repair`의 재사용 가능한 Lean 검증·수리 루프를 다룬다. task 고정, CLI/REPL 결과 계약, native InfoTree 오류 문맥, 최종 전체 파일 재검증, token·heartbeat·API 예산을 포함한다.

- 대표 공유 문서·상세 보고서: [report.md](report.md).
- 측정·검증 요약: [metrics.json](metrics.json).
- 구현 소스: [lean_repair](evidence/verification-repair/lean_repair/).
- 원래 사용법: [보존 README](evidence/verification-repair/README.md).
- 원래 전체 시험: [validation.json](evidence/verification-repair/validation.json) · [시험 로그](evidence/verification-repair/validation-tests.log).
- 재현·실행 안내: [evidence](evidence/README.md).
- 관련 실험: [Warm-up P1–P15](../../refactoring/warmup/손지연/README.md).

원래 73개 테스트 통과는 모의 adapter 시험과 실제 Lean/REPL 통합시험의 결과이며 유료 모델 호출은 0회였다. 이번 정리에서의 unit 검사와 과거 통합시험은 별도로 기록한다. 독립 의미 Comparator·적대적 코드 OS sandbox·공식 Arena worker 동등성은 구현·입증된 것으로 표시하지 않는다.
