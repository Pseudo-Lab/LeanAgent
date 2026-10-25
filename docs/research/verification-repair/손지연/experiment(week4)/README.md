# 손지연 검증·수리 구현과 15문제 실험 · Week 4

손지연의 Week 4(2026-10-25) 준비 자료입니다. Lean 검증·수리 controller와 Warm-up P1–P15 실험을 하나의 연구 보고서로 통합했습니다.

자료 위치는 `docs/research/verification-repair/손지연/experiment(week4)/`입니다. 구현 검증 기록은 2026-10-22, 실제 15문제 실험은 2026-10-24 실행 ID `20261024T000653+0900`을 따릅니다.

- [발표자료 · HTML](presentation.html): 본 발표 20장과 질의응답 부록 6장. 발표 모드·방향키 탐색·발표자 노트·목차·인쇄를 지원합니다.
- [통합 보고서 · HTML](report.html) / [Markdown](report.md): 연구 질문 → 구현·결과 계약 → 실험 설계 → 판정·복구·리팩터링 결과 → 한계·재현 방법.
- [통합 측정 요약](metrics.json): `implementation`은 구현 시험, `experiment`는 실제 15문제 실험 기록입니다.
- [검증 근거와 재현](evidence/README.md): 구현 코드·시험, 실험 데이터·로그, 기록 재생 명령.

| 관측 | 결과 |
| --- | --- |
| 성공 판정 V-A | 90개 fixture에서 종료 코드/goal 기반 판정 각각 오수락 38건, 엄격 판정 0건 |
| 손상 proof 복구 V-B | 180이력 중 123건 성공 |
| 정상 proof 리팩터링 P-A | 180이력 중 생성 후보 96건 선택, 원본 fallback 84건 |
| 기록 재생 / 과거 fresh Lean 재검증 | 360/360 일치 / 1,212/1,213 비교 일치 |

구현의 과거 73개 시험과 실제 구독 모델 호출 795회는 별도 기록입니다. API USD 비용·공식 점수는 미측정이며, 실제 실행 날짜·조건·한계는 통합 보고서에 적었습니다.

```text
experiment(week4)/
├── README.md
├── presentation.html
├── report.md
├── report.html
├── metrics.json
└── evidence/
    ├── README.md
    ├── implementation/  # 검증·수리 코드, 설계, 예제, 시험·검증 기록
    ├── experiment/      # 15문제 harness, 프로토콜, 후보·측정·원시 로그
    └── packaging/       # 보존 기록, 기록 재생 도구, 병합 전 공유 문서
```

관련 자료: [Week 3 · 설계·초기 검증](<../design-and-pilot(week3)/README.md>) · [Week 2 · Warm-up 7·12 풀이](../../../refactoring/warmup/손지연/README.md) · [전체 자료 안내](../README.md).
