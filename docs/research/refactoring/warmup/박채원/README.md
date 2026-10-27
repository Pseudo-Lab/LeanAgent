# 박채원 Warm-up 14·15

2026-10-11 Week 2, 2026-10-18 Week 3 공유 자료. `putnam_1964_b2`와 `putnam_1995_a3`의 문제 해석·풀이·Lean 증명(Week 2)과, 참조 증명과 내 증명을 전체 `import Mathlib`(v4.26.0) 환경에서 측정한 결과, 참조 증명이 어디서 길어졌는지 블록별로 나눈 분석(Week 3), 그리고 2026-10-20–22 블록 분할 기준 학습, Warm-up 15문제 블록 분석, 블록 전략(웜업 15문제)을 다룹니다.

- 발표자료: [presentation.html](presentation.html) (Week 3 발표, Lean Refactor 논문 정리와 15번 블록 조합 실험 포함)
- 상세 보고서: [report.md](report.md) (Week 2 풀이와 Lean 코드)
- 상세 보고서: [local-measurement.md](local-measurement.md) (Week 3 로컬 측정)
- 상세 보고서: [structure-design.md](structure-design.md) (Week 3 참조 증명과 수정한 증명의 블록별 proof token 비교)
- 검증 근거: [evidence/](evidence/) (측정한 Lean 파일, 토큰·블록별 토큰 계산 스크립트, Infoview 출력)
- 검증 근거: [evidence/block-combinations-15/](evidence/block-combinations-15/README.md) (15번 블록 조합 32개 Lean 파일, 생성 스크립트, 토큰·컴파일 결과)
- 검증 근거: [evidence/block-analyzer/](evidence/block-analyzer/README.md) (Warm-up 15문제 블록 분석기와 블록별 proof token 결과)
- 검증 근거: [evidence/block-strategy/](evidence/block-strategy/README.md) (웜업 블록 전략: 규칙 1–8(스택·DFS·해시·편집 거리 DP·우선순위 큐·메모이제이션·트리 DP·분기 합치기)과 미사용 `have` 반복 제거, 웜업 15문제 지정 버전 컴파일 결과와 감소율 신뢰구간)
- 관련 자료: [블록 분할 기준 학습](studies/block-segmentation/README.md) (Lean InfoTree, Strata·CSLib 증명 구조)
- 관련 자료: [Lean&Mathlib 학습·LeanDojo 조사](../../../lean-mathlib/박채원/README.md)
