# 남성우 새 연습문제·로컬 수리 및 minimizer 실험

2026-10-25(일) Week 4 공유. 10월 22일 푸시한 자료를 기준으로 연습 세트 준비, 실제 수리 사례, Warm-up 후처리 평가를 구분해 정리했습니다. 새 Lean 실행 결과를 추가한 작업은 아닙니다.

- 발표자료: [실험 A · Local Proof Minimizer](presentation.html)
- 상세 보고서: [결과 해석과 실패 사례](report.md)
- 측정 기록: [집계 JSON](evidence/local-minimizer-2026-10-21/summary.json) · [15문제 결과 CSV](evidence/local-minimizer-2026-10-21/results.csv)
- 검증 근거: [minimizer 실행·재현](evidence/local-minimizer-2026-10-21/README.md) · [실제 수리 사례·정책 fixture](evidence/validation-mini/README.md) · [원본·이동 해시](provenance.json)
- 연습 세트: [세트별 범위와 검증 상태](datasets.md)
- 관련 자료: [남성우 Agent Repair 연구](../../../agent_repair/남성우/README.md) · [10월 25일 모임](../../../../meetings/2026-10-25-week4/README.md)

## 결과를 읽는 기준

| 자료 | 확인한 범위 | 해석의 한계 |
| --- | --- | --- |
| validation-mini | R01–R08 및 R06b, 실제 Lean 9사례; 합성 정책 43입력·selector 12케이스 | 단일 환경 중심. R06/R06b는 지정 버전 전체 검증이 아님 |
| 별도 연습 JSONL | 문제·환경 메타데이터가 있는 준비된 세트 | 이번 minimizer 성능 평가에 사용하지 않음 |
| minimizer A | Warm-up 15문제·36버전 조합, 최종 선택 36/36 통과 | 기존 선택 증명 후처리 실험. 공식 Arena 제출 아님 |

평균 로컬 점수 35.238 → 35.785(+0.547), 3문제 개선·12문제 유지. P8은 탐색 제외. 추가 모델 API 호출은 0회이며 과거 후보 생성 비용까지 0이라는 뜻은 아닙니다.

문서 정리 검증: [검증 기록](organization-checks.md).
