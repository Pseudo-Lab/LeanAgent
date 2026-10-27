# 손지연 검증·수리 설계와 초기 검증 · Week 3

2026-10-18 Week 3 공유 자료. 작은 REPL 예제로 성공 판정 기준을 살펴보고, Warm-up P7·P12 통제 실험과 P7의 실제 모델 후보 검증을 정리합니다.

- 대표 자료: [검증·수리 설계와 실행 (HTML)](report.html).
- 측정 기록: [metrics.json](evidence/metrics.json).
- 상세·근거 자료: [실험별 Markdown·JSON 요약](evidence/README.md) · [요약 대조·정리 검사](evidence/validation.json).
- 관련 자료: [Warm-up 7·12 풀이](../../../refactoring/warmup/손지연/README.md) · [Week 3 모임](../../../../meetings/2026-10-18-week3/README.md).
- 후속 자료: [Week 4 · 구현·15문제 통합 실험](<../experiment(week4)/README.md>) · [전체 자료 안내](../README.md).

P7·P12의 정상본·알려진 수정본과 P7의 첫 모델 후보 한 건은 기존 실행에서 전체 파일 검증을 통과했습니다. 실제 실패 후 모델 재시도, P12 모델 수리와 피드백 A/B 비교는 미실행입니다. 독립적인 일반 수리 성능으로 집계하지 않습니다.

근거 자료는 문서·JSON 11개로 요약했으며 원본 증명·실행 코드·로그·환경 및 소스 사본은 삭제했습니다. 요약본만으로 전체 실험을 재실행하거나 원시 기록을 재감사할 수 없습니다. 보고서의 코드·로그 발췌와 실행 결과는 당시 기록이며, 이번 정리에서 새 Lean 검증·모델 호출·시험은 수행하지 않았습니다.
