# 권주원 코퍼스 수집·통계 분석

2026-10-18 Week 3 공유 자료. 2026-10-16에 6개 출처의 수집 범위, 증명 길이와 tactic 사용률을 정리하고, 증명 문자열 중복·파일 편중·출처별 가중치의 영향을 추가 분석했습니다.

- 대표 보고서: [수집 코퍼스와 통계 분석 HTML](report.html).
- 통계 기록: [analysis.json](evidence/corpus-survey/analysis.json) · [출처 요약 CSV](evidence/corpus-survey/source-summary.csv).
- 재현 근거: [입력 범위와 재생성 방법](evidence/corpus-survey/README.md) · [검증 기록](evidence/corpus-survey/validation.json).
- 관련 자료: [Warm-up 3·6·13 연구](../../warmup/권주원/README.md) · [Week 3 모임](../../../../meetings/2026-10-18-week3/README.md).

추출 선언 382,121개 중 주 통계는 직접 sorry가 없는 by 증명 323,207개입니다. 길이·빈도 통계와 Lean 검증 비용을 구분하며, 이번 분석에서 Lean 컴파일·커널 검사·heartbeat 측정은 새로 수행하지 않았습니다. Strata의 검증 601개는 이전 기록입니다.

HTML은 데이터를 내장하므로 별도 데이터 서버나 라이브러리 설치 없이 열람할 수 있습니다. 재현 코드에는 저장된 통계로 화면을 재생성하는 모드와, 별도로 준비한 집계 입력으로 통계를 다시 계산하는 모드가 있습니다.
