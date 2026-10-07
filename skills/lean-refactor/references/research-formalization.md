# 큰 연구 형식화에서 배울 검토 방법

기존 Lean 개발을 리팩터링의 교과서로 검토할 때, 또는 표현 사이의 bridge를 수정할 때 읽는다. 원래 문제를 새로 증명하거나 외부 저장소의 코드를 수정할 권한을 암시하지 않는다.

## 1. 수학적 계약을 먼저 읽기

최종 정리에 대해 대상 객체, 가정, 양화사 순서, 결론, 비공허성 조건을 적는다. 정리 이름이나 README만으로 범위를 판단하지 않는다.

- `∃ E, ∀ curve, ...`를 `∀ curve, ∃ E, ...`로 바꾸면 동일한 예외 집합이 모든 곡선을 처리한다는 보장이 사라질 수 있다.
- 예외를 피하는 객체가 존재한다는 조건 없이 예외 밖에서만 성립한다고 하면 공허한 명제가 될 수 있다.
- nonzero, strict inequality, positive degree, repeated components처럼 실제 계약에 포함된 정보는 압축하거나 표현을 바꿀 때 유지한다.

이는 모든 작은 증명에 별도 체크리스트를 강제하는 규칙이 아니다. 실제 명제의 중요한 조건을 찾아 보존하는 방법이다.

## 2. bridge가 보존하는 데이터를 구체화하기

표현 A와 B가 같은 문제를 다룬다는 것을 로컬 대응에서 확인한다. 정리 전체의 `A ↔ B`만 읽고 끝내지 말고, 그 증명이 이용하는 객체별 degree·multiplicity·evaluation 등의 대응을 읽는다.

Nagata 소스에서는 곡선과 방정식 사이에 성분의 가중치를 유지하고, 중복도를 ideal-power 조건과 수치 사이에 연결하며, 실제 basis와 jet map을 수치 행렬에 연결한다. 영점 집합만 같다는 사실은 중복 성분 데이터의 보존을 보장하지 않는다.

## 3. 조건부 정리의 가정을 끝까지 추적하기

`construction → FullTarget`라는 보조정리는 유용한 모듈 계약이다. “중요한 사실을 가정했다”는 이유만으로 전체 증명을 불완전하다고 결론내리지 않는다. 대신 최종 정리에서 그 가정을 어떤 정리로 채우는지 확인한다. 채우는 증명을 못 찾았다면 실제 미확인 지점으로 기록한다.

최종 한 줄짜리 정리는 조립 계층일 수 있다. 그 길이를 전체 증명의 간결성·효율성 증거로 사용하지 않는다.

## 4. 확인 수준을 구분해서 보고하기

| 확인 | 말할 수 있는 것 | 아직 말할 수 없는 것 |
| --- | --- | --- |
| 소스와 keyword 검색 | 읽은 범위에 특정 토큰이 발견됐는지 | kernel 검증·추이적 공리 목록 |
| import 그래프 | 모듈 문맥의 연결 | 최종 proof term의 실제 의존성 |
| 고정 환경 빌드 | 해당 환경에서 컴파일된 결과 | 자연어 명제의 충실성 전체 |
| `#print axioms` 실행 | 해당 정리의 실제 공리 의존성 | 허용 목록만 읽은 결과와 동일하지 않음 |
| 독립 checker 실행 | 그 checker 설정에서 나온 결과 | 설정 파일만 있는 경우의 실행 성공 |

설정에 따라 독립 checker를 생략하거나 여러 종류를 사용할 수 있다. 요청된 검토 범위와 실제 제공 도구에 맞춰 결정한다. 설치되지 않은 toolchain과 의존성을 대체 버전으로 실행한 결과를 원본 검증이라고 부르지 않는다.

## Nagata 사례의 근거

검토 revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, 2026-10-07. pinned Lean `v4.34.1`. 이번 검토는 소스 분석으로, build·axiom 출력·Comparator는 실행하지 않았다.

- [최종 조립](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/Nagata.lean): `fullNagata_iff_effectiveCurves`, `nagata_full`, 최종 두 정리.
- [정규화된 목표와 조건부 인터페이스](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/FullTarget.lean): `fullNagata_of_genuine_source_construction`.
- [필요한 기하학적 construction 해소](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/FixedCurveSections.lean): `source_fixed_scaled_construction`.
- [실제 basis/jet map과 행렬](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/MatrixLimits.lean): `basisJetMatrix_mulVec_repr`, `not_eventually_nonzero_kernel_of_injective_limit`.
- [비교 설정](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Nagata.json): 허용 공리 `propext`, `Quot.sound`, `Classical.choice`; `enable_nanoda: false`.

이 사례는 검토 방법의 근거이며 특정 tactic 또는 도구의 의무 사용 규칙은 아니다.
