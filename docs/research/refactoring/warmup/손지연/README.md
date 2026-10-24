# 손지연 Warm-up 7·12

Week 2 공유 자료. 명제 해석, 원본·수정 코드, 실패·해결 과정과 평가를 정리합니다.

- [발표자료](presentation.html).
- [상세 보고서](report.md).
- [측정 기록](metrics.json).
- [ATP 논문 발표](../../../automated-theorem-proving/손지연/README.md).
- [Week 3 검증·수리 보고서와 실험 요약](../../../verification-repair/손지연/README.md).

별도 증명 소스·스크립트·원시 로그는 작성자의 로컬 작업 자료이며, 이 공유 묶음에 있는 측정 JSON과 구분합니다.

## Week 4 후속 통합 실험 · 2026-10-25 공유

2026-10-24 실행한 정상 proof 리팩터링과 손상 proof 검증·수리를 Warm-up P1–P15 전체에 적용한 후속 실험입니다. 기존 P7·P12 발표·보고서·측정 기록은 유지합니다.

- 대표 공유 자료: [15문제 실험 HTML](verification-repair-experiment.html).
- 상세 보고서: [실험 결과 Markdown](verification-repair-experiment.md).
- 측정 기록: [experiment-metrics.json](experiment-metrics.json).
- 검증 근거와 기록 재생: [evidence 안내](evidence/README.md).
- 관련 구현: [Verifier-guided Agent 검증·수리 구현](../../../verifier-guided-agent/손지연/README.md).

P-A 최종 검증 180건에는 새 후보 선택 96건과 원본 fallback 84건이 포함됩니다. V-B 복구 성공은 123/180건입니다. 구독 모델 호출 실험이며 API USD 3 준수·공식 점수는 미확정입니다. 저장된 360개 이력의 기록 재생과 과거 Lean 재검증 1,213건을 새 모델 독립 실행과 구분합니다.
