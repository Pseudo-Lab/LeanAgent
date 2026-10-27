# 박선영 Warm-up 8·11

Week 2 공유 자료. 증명 구조 분석과 리팩터링 후보, 검증·측정 절차를 다룹니다. 원본 실측(2026-10-15)에 이어 두 후보 모두 v4.31.0 컴파일·공리 검사·heartbeat 측정에 통과했습니다(2026-10-16). 8번은 토큰 증가·heartbeat 감소의 절충안, 11번은 두 지표 모두 감소한 후보입니다. 당시 로컬 검사는 v4.31.0만 수행했습니다. 외부 대시보드의 후속 재검증과는 구분합니다.

2026-10-17 후속 업데이트: P11 순차 탐색에 이어 B / B+A / B+C / B+A+C를 고정 비교했습니다. 이 정리·환경에서는 C가 A 없이도 786 heartbeat를 줄였으며, 결합 후보는 세션 best로만 기록하고 기존 선택 후보와 구분합니다. 다른 정리에서의 효과나 에이전트 전략 선택 능력의 일반화된 향상은 아직 확인하지 않았습니다.

2026-10-18 발표 재구성: P11 실험의 질문·변경 가설·통제 설계·결과 해석을 본론으로 확장했습니다. 측정일은 2026-10-17이며 새 Lean 실험은 수행하지 않았습니다. Lean 기초·P8 풀이·대회 규칙·초기 검증 표는 같은 HTML의 부록으로 보존합니다.

- 이번 주 발표: [Week 4 구조 실험](presentation.html) — **이번 주 내용만 9장**, 지난주는 출발점 설명만 남겼습니다. 각 장의 ‘발표 메모’ 또는 N 키로 말할 내용을 펼칠 수 있습니다. [전체 발표 원고](week4-speaker-notes.md)는 약 7–9분 분량입니다.
- 이전 자료: [지난주 설명·기초 부록을 포함한 통합본](presentation-history-2026-10-25.html) — 16장 + 부록 6장 당시 상태를 보존했습니다. 최신 결과는 이번 주 발표와 아래 보고서를 봅니다.
- 후속 실험: [A/C 효과 분리 확인 보고서](evidence/agent/p11-20261017-ac-check4/report.md) · [앞선 순차 탐색 보고서](evidence/agent/p11-20261017-adaptive3/report.md).
- Week 4(2026-10-25): [전략별 실행 결과](evidence/structural-strategies-2026-10-22/report.md) · [사전 적용 검토·실험 설계](evidence/structural-strategies-2026-10-22/README.md) · [반복 측정 요약](evidence/metrics/structural-pilot-2026-10-25/summary.json). P11의 S1/S2는 개선, S3은 토큰 감소·HB 악화이며 각각 2회 확인했습니다. P12는 원본 의존성 오류로 후보 미실행, P3/P6는 환경 준비 필요입니다.
- 큰 구조 변경 탐색(2026-10-25): [P8·P11 최종 결과와 효과 분석](evidence/performance-search-2026-10-25/report.md) · [프로토콜](evidence/performance-search-2026-10-25/protocol.md). 원본·기존 best·최종 후보를 각각 3회 확인했습니다. P8 **1,320 HB/412토큰 → 380 HB/382토큰**, P11 **38,337 HB/1,379토큰 → 21,010 HB/966토큰**입니다. 기존 best 대비 HB는 각각 71.21%, 45.20% 감소했습니다. 두 지표 모두 개선됐으며 지정 전체 버전·일반화·제출은 미검증/미실행입니다.
- 상세 보고서: [원본 실측·후보 변경점·재현 명령](report.md).
- 측정 기록: [개인 evidence/metrics 집계](evidence/metrics/metrics.json) · [환경·실행 승인·검증기 수정 이력](evidence/metrics/environment-status.json).
- 검증 근거: [원본·초안·재현 코드](evidence/) · [측정 저장 위치 안내](evidence/metrics/README.md).
- 구조·전략 실험: 로컬 `/lean-refactor` skill을 사용했습니다. skill·세션 helper 소스는 이번 공유에 포함하지 않으며 이번 경로 정리에서도 변경하지 않습니다. 후보·가설은 `evidence/agent/<session>/`, 세션 상태·실측·회고는 `evidence/metrics/agent/<session>/`에 보존하며, 공개된 개별 후보 검증은 `evidence/run_experiments.py`를 사용합니다.
- 관련 자료: [별도 Autoformalization 조사·발표](../../../autoformalization/박선영/README.md).

증명·재현 코드는 이 폴더의 `evidence/`에, 실행별 JSON·원시 로그는 그 안의 `evidence/metrics/`에 보관합니다. 미검증 초안을 검증된 선택 후보로 표시하지 않습니다.

이동한 원시 JSON·로그·snapshot은 내용 그대로 보존했습니다. 내부의 과거 출력 경로와 해시·fingerprint는 원래 실행 시점의 기록이며 현재 트리의 경로나 동일성 보장이 아닙니다. 기존 세션을 자동 재개하거나 원장을 새 경로로 고쳐 이어 실행하지 않으며, 후속 실행은 별도 승인·환경 확인 후 새 세션에서 진행합니다.
