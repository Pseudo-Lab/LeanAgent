# 손지연 Warm-up P1–P15 검증·수리 실험

공유 정리일: 2026-10-24. 원래 담당 P7·P12에서 확장한 15문제 통합 실험이다. 실행 ID는 `20261024T000653+0900`이며 정상 proof 리팩터링(P)과 의도적으로 손상한 proof의 검증·수리(V)를 다룬다. 특정 모임이나 새 발표 슬라이드는 이번 요청에 없다.

- 대표 공유 문서: [실험 결과 HTML](verification-repair-experiment.html).
- 상세 보고서: [실험 결과 Markdown](verification-repair-experiment.md).
- 측정 기록: [experiment-metrics.json](experiment-metrics.json).
- 검증 근거와 재현: [evidence 안내](evidence/README.md).
- 관련 구현: [Verifier-guided Agent 구현 설명](../../../verifier-guided-agent/손지연/README.md).

모든 15문제에 P-A 180이력·V-A 90사례·V-B 180이력을 진행했다. P-A 최종 검증 180건에는 새 후보 선택 96건과 원본 fallback 84건이 포함된다. V-B 수리 성공은 123/180이다. V-C 기록 재생 360/360 일치와 기존 Lean fresh 재검증 1,213건은 서로 다른 결과다.

실제 모델은 기존 GPT 구독으로 호출했다. OpenRouter API의 USD 3 준수·공식 점수는 확인하지 못했고, 사용량 불명 1회·soft token cap 초과 2건을 기록했다. 이번 자료 정리는 새 모델 호출이나 Lean 실험을 수행한 것이 아니다.

기존 저장소의 P7·P12 `report.md`·`metrics.json`과 이번 P1–P15 후속 실험을 혼동하거나 덮어쓰지 않도록 별도 파일명을 사용했다. 원본 증명·측정·로그는 evidence 안에 내용 변경 없이 보존했다.
