# Refactoring 연구 자료

대회 문제의 명제 해석, 참조 증명 분석, 개선 시도, 검증 결과와 발표자료를 세트별로 모읍니다.

- [Warm-up 15문제](warmup/README.md): 담당자별 문제 자료와 후속 실험 안내.
- [손지연 Week 4 · 검증·수리 구현과 P1–P15 통합 실험](<../verification-repair/손지연/experiment(week4)/README.md>): 정상 proof 리팩터링, 성공 판정·손상 proof 복구, 선택 정책과 재현성 비교.
- [Arena 개발·실험·운영 가이드(HTML)](arena-guide.html): 에이전트 개발 개요, 문제별 환경 고정 가안·2문제·4환경 파일럿 검증, 대시보드 사용·데이터 갱신·배포, 6개 데이터 출처·후보군 분석, 서브에이전트 effort 비교·재현성 실험. 구현 코드는 별도 `LeanAgent-LeanRefactorArena` 리포에서 관리합니다.
- [수집 코퍼스](corpus/README.md): 출처별 수집 범위·증명 통계와 후속 실험 표본 분석.
- [폴더·파일명 지침](../../STRUCTURE.md).

## 분류 기준

`refactoring/<세트>/<발표자>/`를 사용합니다. 현재 세트는 `warmup`입니다. 발표자료가 여러 문제를 함께 설명하므로 작성자별 묶음을 유지하며, 문제별 증명과 로그는 각 묶음의 `evidence/`에서 관리합니다. 모임 날짜와 문제 번호는 README에 기록합니다.

## 공유 파일의 Warm-up·논문 조사 혼합 여부

2026-10-13에 Week 2 공유 자료를 확인했습니다. 논문을 인용하거나 일반적인 적용 아이디어를 설명하는 것과, 담당 문제 연구 및 논문 조사 발표를 한 파일에 넣은 경우를 구분합니다.

| 발표자 | 확인 결과 | 보관·연결 방식 |
| --- | --- | --- |
| 권주원 | 3·6·13 발표와 ATP 발표는 별도 파일. 입문 학습 노트는 두 주제를 함께 다루는 진행 중 보조 자료 | [Warm-up](warmup/권주원/README.md) · [ATP](../automated-theorem-proving/권주원/README.md) |
| 손지연 | 7·12 발표·보고서와 ATP 발표가 분리됨 | [Warm-up](warmup/손지연/README.md) · [ATP](../automated-theorem-proving/손지연/README.md) |
| 박채원 | 14·15 보고서와 MIL·LeanDojo 연구 문서가 분리됨 | [Warm-up](warmup/박채원/README.md) · [Lean&Mathlib](../lean-mathlib/박채원/README.md) |
| 박선영 | 8·11 발표와 Autoformalization 조사·발표가 분리됨 | [Warm-up](warmup/박선영/README.md) · [Autoformalization](../autoformalization/박선영/README.md) |
| 남성우 | 실제 1·2 풀이 파일은 별도. 연구 발표는 Autoformalization과 Arena 적용·실험 제안을 함께 설명함 | [Warm-up](warmup/남성우/README.md) · [Autoformalization](../autoformalization/남성우/README.md) |
| 정소미 | 같은 슬라이드에 4·9 실험과 Lean Refactor 및 관련 논문 예비 조사가 포함됨. 논문 MD는 별도로 존재 | [공유 슬라이드](warmup/정소미/presentation.html)를 Warm-up에 두고 [연구 폴더](../verifier-guided-agent/정소미/README.md)에서도 연결 |
| 박성호 | 5·10 보고서에 방법·논문 적용과 참고문헌이 포함됨. 별도 논문 조사 발표파일은 현재 없음 | [Warm-up](warmup/박성호/README.md) |

혼합된 슬라이드의 본문은 분할하지 않았습니다. 각 발표의 흐름을 유지하며 한 원본을 공유합니다.

손지연의 후속 검증·수리 자료는 [별도 연구 폴더](../verification-repair/손지연/README.md)에 보관합니다. Week 3 설계·초기 검증과 Week 4 구현·15문제 실험을 구분하며, Week 2의 P7·P12 풀이·ATP 발표는 기존 위치를 유지합니다.
