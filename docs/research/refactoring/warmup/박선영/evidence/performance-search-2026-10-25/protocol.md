# 구조 변경 성능 탐색 — 실행 프로토콜

2026-10-25. 기존 best에서 출발하는 성능 탐색이다. 원본을 부모로 했던 S1/S2/S3 효과 분리 파일럿과 다른 실험이며, 두 세션의 수치를 섞어 인과 대비를 만들지 않는다. 공식 점수·자동 채택·제출이 아니다.

## 고정 범위

- P11: 과거 B+A+C (`../agent/p11-20261017-ac-check4/attempts/a004/candidate.lean`)를 시작점으로 재검증한다.
- P8: 기존 `../P8/selected.lean`을 시작점으로 재검증한다.
- 기존 로컬 ArkLib/cslib v4.31.0 checkout만 사용한다. 설치·다운로드·의존성 빌드를 하지 않는다.
- 문제당 새 후보 최대 6개. 수리도 새 후보이며 예산을 소비한다. 첫 준비 배치는 최대 2개다. 예산을 반드시 다 쓸 필요는 없다.
- 큰 블록의 기존 보조정리 대체(T1), 실질적 반복 논증 공통화(T2), 귀납·중간 명제 등 증명 골격 변경(T3)을 허용한다.
- 모든 변경은 대상 proof 내부. statement/가정/import/option/주변 선언을 유지한다. 새 보조 사실은 비용에 포함되는 지역 `have`로 제한한다. 순환 참조·후속 정리 사용은 검토로 배제한다.
- 과거 원장, 선택 proof, `STRUCTURE.md`, `Agents.md`, 로컬 skill은 변경하지 않는다.

## 준비와 실행을 구분

후보 독해·작성은 병렬, 실제 Lean 프로세스는 직렬이다. 도구 호출 오류로 처음 준비 워크플로의 세 작성 에이전트가 모두 정상 보고서를 반환하지 못했다. P8 후보 두 개만 파일로 남았으며, 최초 독립 검토는 이 두 후보의 정적 계약과 부모 해시만 확인했다. 이를 컴파일 성공이나 전체 실행기 승인으로 해석하지 않는다.

`run_search.py`는 기존 `run_experiments.py.evaluate`를 호출하는 별도 어댑터다. 기존 검증/계측 구현을 바꾸지 않는다. 실제 실행 전 mock 테스트와 실행기 검토를 마친 뒤 최초 초기화 시 코드를 고정한다. 고정 뒤 코드 변경이 필요하면 기존 세션을 재개하지 않고 새 실험 ID로 분리한다.

## 기록과 중단

- 새 원장: `../metrics/performance-search-2026-10-25/P8/`, `P11/`.
- 초기화 때 원본·시작 proof를 복사하고 source/toolchain/manifest/실행기/공유 helper/benchmark/설치된 Lean·Lake/계측 모듈의 SHA-256을 고정한다.
- 후보의 사전 가설·부모·본문을 등록 시 복사한다. 모든 파일을 exclusive create로 생성한다. 실행한 후보를 수정하지 않는다.
- 본문 중복 검사는 마지막 개행 제거 후 SHA-256이다. 공백/주석의 의미적 동등성까지 판정하지 않는다. 등록이 중단되어 남은 예약 디렉터리도 예산을 사용한다.
- 실험 전체에 exclusive lock 하나를 사용한다. 실행 전 started marker, 종료 후 별도 review를 기록한다. raw 결과는 수정하지 않는다.
- 원본 1회가 통과하기 전 start/후보 금지, start 1회가 통과하기 전 새 후보 금지. 원본 실패·중단, 환경 오류, 도구 오류, fingerprint 변경은 해당 정리를 중단한다.
- 원본 공리 대비 부분집합 검사를 추가한다. raw `passed`가 있더라도 새 공리·HB 누락·사후 fingerprint 변경이 있으면 승인하지 않는다.
- 명령별 timeout 180초. 실패 후보를 자동 재실행·수리하지 않는다. 수리는 다른 번호로 등록한다.
- 다른 로컬 프로세스가 의존성을 동시에 변경하지 않는다는 운영 조건이 필요하다. 전체 transitive `.olean` 캐시를 재현 가능한 hermetic build로 고정하는 장치는 아니며, 정적 금지 패턴 검사도 임의 악성 Lean 코드를 위한 보안 sandbox가 아니다.

## 측정과 판단

원본·시작점·선택한 최종 후보는 각 3회 독립 프로세스로 확인한다. 후보 screening은 1회이며, 통과한 후보에 한해 2·3회 확인할 수 있다. 중앙값·최솟값·최댓값을 제시한다. 세 번 모두 통과한 항목만 확정 비교를 생성한다. 반복이 같더라도 다른 머신·버전 재현성이나 통계적 유의성을 주장하지 않는다.

원본과 시작 best 각각에 대한 토큰/HB 변화율을 구분한다. 유효성이 전제이며 HB 우선, 동률이면 토큰을 본다. 토큰/HB tradeoff 후보는 별도 보존한다. 스크립트는 `selected.lean`을 자동 교체하지 않는다.

유망한 변화가 나오면 독립적으로 조합 가능한 변경에 한해 best / best+A / best+B / best+A+B 효과 분리를 별도 설계한다. 종속 변경을 억지로 분리하지 않는다. 다른 정리 전이는 적용 조건을 고정한 다음 단계이며 이번 두 정리만으로 일반화하지 않는다.

## 명령 형태

저장소 루트에서 실행한다. 초기화·등록·실행은 overwrite 보호가 있으므로 이미 실행한 명령을 그대로 반복하지 않는다.

```sh
SEARCH=docs/research/refactoring/warmup/박선영/evidence/performance-search-2026-10-25/run_search.py
python3 -I "$SEARCH" initialize --problem 8 --repo <기존-cslib-checkout> --start docs/research/refactoring/warmup/박선영/evidence/P8/selected.lean
python3 -I "$SEARCH" register --problem 8 --candidate <새-candidate.lean> --hypothesis <사전-hypothesis.json>
python3 -I "$SEARCH" run --problem 8 --name reference --repetition 1
python3 -I "$SEARCH" run --problem 8 --name start --repetition 1
python3 -I "$SEARCH" run --problem 8 --name c001 --repetition 1
python3 -I "$SEARCH" summarize --problem 8
```

최종 결과와 실제 실행 여부는 별도 `report.md` 및 원장으로 확인한다. 이 프로토콜은 성능 향상이 이미 나왔다는 보고서가 아니다.
