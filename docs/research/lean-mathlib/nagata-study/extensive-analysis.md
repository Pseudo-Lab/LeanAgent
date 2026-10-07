# Nagata 형식화를 교과서로 읽기

개인 공부용 상세 분석 · 2026-10-07

## 1. 무엇을 검토했는가

대상은 [OpenAI의 math 저장소](https://github.com/openai/math)의 **평면곡선에 대한 Nagata conjecture** 형식화다. 다항식 자기동형에 관한 같은 이름의 문제와 구별해야 한다. 저장소는 이 추측의 증명을 제시한다. 이 문서는 그 개발의 수학적 인터페이스와 Lean 증명 구조를 읽고, 우리가 Lean 리팩터링을 할 때 재사용할 원칙을 정리한다. 전체 수학적 증명의 독립적인 검증 보고서는 아니다.

검토 revision은 `adc7f1241b42e322a6451854ab7e4b4c146bf78a`다. 저장소 전체가 아니라 `PlaneCurves` 소스, Nagata의 Comparator 명세, 해당 논문의 TeX 소스, 환경 설정을 선택해서 내려받았다. 실제 읽기는 최종 정리, 표현 간 연결, 곡선 방정식 실현, 일반성, 기하적 구성, 행렬 극한, 보간에 집중했다. 117개 파일 각각의 모든 proof body를 줄 단위로 검토하지는 않았다.

| 증거 | 이번에 확인한 것 | 아직 확인하지 않은 것 |
|---|---|---|
| 소스 | 정의, 주요 증명 연결, 구현 키워드 검색 | 모든 수학적 논증의 독립 검토 |
| import | Nagata에서 도달하는 로컬 모듈 117개 | 최종 proof term의 실제 선언 의존성 |
| 환경 | Lean `v4.34.1`, Mathlib 고정 revision | 그 환경에서의 빌드 |
| 공리 | 허용 공리 설정 | 최종 정리의 `#print axioms` 출력 |
| 별도 검사 | Comparator 설정 및 challenge 명세 | Comparator 실행 성공, nanoda 실행 |

관련 구현 117개 파일은 총 36,997줄이다. 주석·문자열을 가린 검색에서 `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by`, `run_tac` 토큰은 나오지 않았다. 이는 제한된 소스 관찰이다. Mathlib는 이 검색 범위 밖이고, 매크로·간접 의존성·proof term을 판정하는 Lean 검사기도 아니다. 재현 가능한 목록과 파일 해시는 [source-audit.json](source-audit.json), 검색 코드는 [scan_sources.py](scan_sources.py)에 있다.

## 2. 문제부터 이해하기: 곡선의 복잡도와 통과 비용

종이에 점을 여러 개 찍고, 하나의 곡선을 그 점들에 통과시킨다고 생각하자. 직선은 자유도가 적다. 차수가 큰 다항식으로 만든 곡선은 더 복잡해서 여러 조건을 감당할 수 있다. 여기서 **차수 d**는 곡선의 복잡도 예산이다.

점 하나를 그냥 지나가는 것보다 그 점에서 여러 번 겹치거나 높은 차수로 사라지는 것은 더 많은 조건을 요구한다. 이 부담이 **multiplicity m**, 즉 소멸 중복도다. 예를 들어 국소 방정식 `y`와 `y²`는 둘 다 같은 직선 위에서 0이 되지만, 직선 위 점에서 소멸하는 차수는 각각 1과 2다.

Nagata의 부등식은 매우 일반적인 r개의 점에 대해 다음을 말한다.

> r ≥ 10이면, 비영 동차다항식으로 정의된 양의 차수 곡선의 점별 중복도 합은 d√r보다 엄격하게 작다.

수식은 `m₁ + … + mᵣ < d√r`다. 모든 중복도가 m으로 같다면 `d > m√r`로 읽을 수 있다. 서로 다른 중복도도 포함하며, 곡선이 여러 성분으로 쪼개지거나 같은 성분이 반복되는 경우도 포함한다.

왜 √r일까? 평면에서 차수 d의 계수 개수는 대략 d²/2이고, 한 점에서 중복도 m을 강제하는 조건 수는 대략 m²/2이다. r개의 점이면 부담은 대략 rm²/2이므로 d²와 rm²를 비교하면 √r가 보인다. **이 차원 계산은 직관이지 증명이 아니다.** 조건들이 독립이라는 점과 경계에서의 엄격 부등식을 별도로 해결해야 한다.

왜 10부터일까? 9개의 점에는 그 점들을 지나는 cubic, 즉 3차 곡선을 찾을 수 있고, 중복도 1씩이면 합 9와 `3√9 = 9`가 같아진다. 따라서 같은 엄격 부등식을 r=9에 그대로 요구할 수 없다. 이 예는 논문의 cubic 중심 구성도 이해하는 출발점이다.

명세의 정확한 범위는 [039 설명](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/docs/039.md)과 [FullNagata 정의](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/Configuration.lean#L312)를 함께 읽어야 한다.

## 3. “매우 일반적인 점”은 숨은 조건이 아니라 정리의 일부다

이 정리는 임의의 점 배치에 대한 주장이 아니다. 모든 점이 같은 직선 위에 있으면 직선 하나가 모든 점을 지나며 부등식을 쉽게 위반한다. 특별한 배치를 제외하는 장치가 필요하다.

형식화는 순서가 있고 서로 다른 점들의 configuration 공간에서, 가산 개의 proper closed set을 예외로 둔다. 중요한 것은 한 곡선을 볼 때마다 예외를 새로 고르는 것이 아니라, **하나의 예외 집합열을 먼저 고르고 그 밖의 점 배치에서는 모든 곡선에 대해 부등식이 성립**한다는 점이다.

실제 Lean 문법을 단순화한 양화사 골격은 다음과 같다.

```text
모든 r ≥ 10에 대해
  예외 집합열 E₀, E₁, … 가 존재하고
  각 Eₙ은 닫혀 있으며 전체 공간과 다르고
  모든 Eₙ을 동시에 피하는 점 배치가 존재하며
  Eₙ들을 피하는 모든 점 배치 p에 대해
    모든 양의 차수 d, 비영 동차식 F, 중복도 하한 m에 대해
      F가 p에서 m 이상의 중복도를 가지면 ∑m < d√r
```

`∃E ∀F`를 `∀F ∃E`로 바꾸면 훨씬 약한 명제가 된다. 또한 “각 Eₙ이 전체 공간이 아니다”만으로 합집합을 피할 점의 존재가 자동으로 따라오지는 않는다. 예를 들어 가산 집합은 singleton들의 가산 합집합으로 전부 덮인다. 이 형식화는 비어 있지 않은 공통 여집합을 명시적으로 요구하고 구성한다.

[Avoidance.lean의 회피 정리](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/Avoidance.lean#L129)를 읽으면 이 역할이 분리되어 있다. 일반적인 가산성 도구가 있다는 사실만으로 닫힘·properness까지 이미 해결되었다고 읽지 말아야 한다. 각각의 가정을 실제로 충족하는 부분을 찾아야 한다.

**리팩터링 교훈:** 명제의 binder만 보존해도 정의 안의 양화사나 조건을 바꾸면 의미가 달라진다. 정의를 만지는 작업에서는 양화사 순서와 비공허성 조건을 별도의 계약으로 기록한다.

## 4. 같은 곡선을 왜 여러 방식으로 표현하는가

사람은 “곡선”이라는 말 하나로 여러 대상을 오간다. Lean에서는 그 이동이 정리로 드러난다.

| 표현 | 담고 있는 정보 | 유리한 작업 |
|---|---|---|
| 비영 동차다항식 | 계수, 전체 차수, 방정식 | 계수 공간·대수 계산 |
| 동차 주아이디얼 | 상수배에 무관한 방정식 | associate/unit 처리 |
| 유효 곡선 cycle | 소수 성분과 각 성분의 양의 정수 가중치 | 분해·곱·반복 성분 |
| 국소 아이디얼의 거듭제곱 | 지정 점에서의 소멸 차수 하한 | multiplicity 조건 |
| Taylor 계수/jet | 소멸 조건을 유한 선형 조건으로 표현 | 행렬·극한·rank |

특히 cycle을 단순한 점집합이나 radical ideal로 바꾸면 반복 성분 정보가 사라진다. `y`와 `y²`가 같은 영점집합을 가진다는 이유로 합치는 리팩터링은 이 문제의 핵심 데이터를 잃는다.

[EffectiveCurves.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/EffectiveCurves.lean#L83)은 실제 동차식으로 cycle을 실현하고, 선택된 방정식으로 차수와 multiplicity를 정의한 뒤, 다른 방정식 선택에도 값이 유지됨을 연결한다. `Classical.choose`로 방정식을 하나 고른 것 자체가 완성은 아니다. 선택이 관찰 가능한 수학적 값에 영향을 주지 않는다는 증명이 뒤따라야 한다.

## 5. Bridge lemma: 번역이 의미를 보존한다는 보증서

최종 정리 근처의 `iff` 정리들은 장식이 아니다. 서로 다른 언어로 쓴 동일한 주장을 연결하는 인터페이스다.

```text
FullNagata: 동차식 + multiplicity 하한
      ↕ 하한 조건과 실제 중복도 연결
ordinary multiplicity 버전
      ↕ 방정식 선택·성분 가중치의 불변성
effective curve/cycle 버전

기하학적 section
      → 실제 source space의 벡터
      → 선택한 basis에서 좌표
      → jet 행렬의 kernel 벡터
```

검토할 때는 `iff`라는 이름보다 양쪽 정의의 데이터와 증명을 읽는다. 상수배로 방정식을 바꾸어도 중복도가 유지되는지, 차수가 같은지, 모든 반복 성분을 반영하는지, 비영성이 전달되는지를 확인한다.

추천 읽기:

- [IdealCycles의 방정식 실현 정리](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/IdealCycles.lean#L242): 양의 차수 방정식이 존재한다는 실질적인 연결.
- [CycleMultiplicity의 연결](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/CycleMultiplicity.lean#L397): multiplicity 하한, 실제 수치, 성분별 합 사이의 관계.
- [FullTarget의 버전 연결](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/FullTarget.lean#L41): 최종 명제의 표현을 바꾸는 정리.

**리팩터링 교훈:** 표현 전환을 공통 보조정리로 만들면 반복 증명이 줄고 정의 변경의 영향이 모인다. 단, bridge가 계산을 더 비싸게 만들 수도 있다. 가독성 향상과 처리 비용 감소를 따로 측정한다.

## 6. 최종 몇 줄에서 실제 증명까지 거꾸로 내려가기

[Nagata.lean의 최종 좌표 정리](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/Nagata.lean#L162)는 이미 증명한 `W13.nagata_full`을 사용한다. 이 한 줄을 “추측을 한 줄로 풀었다”거나 proof token 비용 전체로 해석하면 안 된다. 해당 파일은 169줄이고, 연결된 로컬 import 모듈 전체는 36,997줄이다. 이 수도 proof term 크기와는 다르다.

핵심 조립 지점은 [nagata_full](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/Nagata.lean#L102)이다. 대략 다음 계약을 채운다.

1. 실제 source construction이 있으면 FullNagata를 얻는 일반 정리를 적용한다.
2. 정리가 요구하는 r, 차수, multiplicity, scaling, 점 배치 등의 변수를 받는다.
3. `source_fixed_scaled_construction`으로 요구하는 구성을 제공한다.

여기서 `_hd`, `_hm`처럼 밑줄이 붙은 가설은 해당 proof body에서 쓰이지 않는 변수다. 곧바로 “가정이 사라졌다”는 뜻은 아니다. 적용한 구성 정리가 그 인터페이스보다 강한 범위에서 작동할 수 있다. 실제로 r≥10에서 r≥9를 얻어 구성 정리에 전달하는 부분이 보인다.

검토는 최종 선언 → 조립 정리 → 조건부 정리 → 조건을 충족하는 구성의 순서로 내려가는 편이 효율적이다. 모듈명 `W13`, `W30` 등으로 작성 주체나 모델 작업 방식까지 추론하지 않는다. 소스가 보여 주는 것은 namespace와 의존 관계다.

## 7. 조건부 정리의 가정은 어디서 해소되는가

[FullTarget의 nonsquare reduction](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/FullTarget.lean#L212)은 nonsquare r에서 내부 구간 `3 < d/m < √r`에 있는 universal support를 배제하는 가정을 받아 전체 명제로 올린다. square 경우는 별도로 처리하고, cubic에서 오는 낮은 경계와 산술 조건을 사용해 필요한 범위를 줄인다.

[fullNagata_of_genuine_source_construction](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/FullTarget.lean#L246)은 기하적 구성이 존재한다면 모순을 얻는 구조다. 따라서 이 선언 하나만 읽고 “핵심 기하학을 가정했다”고 결론 내리거나 “이미 기하학까지 증명했다”고 결론 내리는 것은 모두 성급하다.

실제 조립은 [FixedCurveSections의 scaled construction](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/FixedCurveSections.lean#L138)과 [BasisNoncancellation의 기하적 모순](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/BasisNoncancellation.lean#L393)으로 이어진다. 전자는 실제 smooth geometry와 필요한 section을 source 인터페이스에 넣고, 후자는 실제 basis/jet map과 계산 가능한 행렬을 연결한다.

이 단계에서 확인할 질문은 세 개다. “추상 대상이 존재한다고만 했는가?”, “그 대상이 원래 곡선에서 왔는가?”, “필요한 비영성·차수·jet 조건이 같이 전달되었는가?” 구조체 안에 필드를 넣었다는 사실과 필드를 실제 데이터로 구성했다는 사실을 분리해서 읽는다.

## 8. 논문의 큰 전략을 초보자의 언어로

해당 [논문 소스](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nagatas-Conjecture-for-Plane-Curves-September-23-2026/build)의 전개를 Lean 인터페이스와 함께 보면 다음 흐름을 읽을 수 있다. 아래는 논문의 주장과 구현 구조에 대한 요약이며, 그 전체 수학적 정당성을 새로 증명한 것은 아니다.

**① 일반 문제를 다루기 좋은 반례로 좁힌다.** 계수와 점의 incidence를 통해 “일반적인 점 배치에서도 위반 곡선이 존재한다”는 가정을 다룬다. 점들을 순환시켜 만든 곡선들을 곱하면 중복도를 같게 만드는 전략을 사용할 수 있다. 곱하면 차수와 multiplicity가 함께 더해져 비율을 추적할 수 있다. 여기에 square 경우와 cubic 경계를 이용한 환원이 들어간다.

**② 점들을 특별한 모양으로 움직인다.** elliptic cubic 위의 9개 기준점과 나머지 r−9개의 점을 이용한다. 점들이 충돌하는 극한을 보되, 처음부터 특별 배치 하나를 최종 명제의 일반 배치라고 착각하지 않는다. 일반 배치에 대한 가정에서 얻은 데이터가 이 가족을 따라 전달되는 구조가 필요하다.

**③ 기하학을 선형대수로 옮긴다.** 곡선으로부터 section을 얻고, section의 소멸 조건을 jet 조건으로 바꾼다. basis에서 section을 표현하면 조건은 행렬 곱이 0이라는 식이 된다. 곡선이 존재한다는 가정은 이 행렬에 비영 kernel 벡터가 존재한다는 주장으로 전달된다.

**④ 극한 행렬은 kernel이 없다고 보인다.** 정규화된 theta basis의 극한이 지수형 함수와 연결되고, 미분값은 거듭제곱형 행렬 항으로 연결된다. 보간과 다항식 공간의 차수·폭 계산으로 injectivity를 얻는다. scaling은 정수 경계 오차를 처리하는 데 쓰인다.

**⑤ 두 결론이 충돌한다.** 가까운 configuration마다 비영 kernel이 있어야 하는데, 극한 행렬이 injective이면 충분히 가까운 행렬도 injective이다. 이 모순이 환원한 반례를 배제한다.

각 화살표에는 비영성, 차수, 점의 구별, 좌표변환, 극한의 정당성을 보존하는 연결이 들어간다. 초보자는 theta 함수부터 정복하려 하기보다 이 다섯 단계의 입출력을 먼저 이해하는 편이 좋다.

## 9. 가장 재사용하기 좋은 아이디어: kernel 벡터를 연속으로 고르지 않아도 된다

어떤 매개변수 t에 따라 행렬 A(t)가 변한다고 하자. 매 t에서 `A(t)v = 0`인 비영 v가 존재해도, 그 벡터들을 연속 함수 v(t)로 고르기는 어려울 수 있다. 하지만 최종 목적이 “가까운 곳에는 kernel이 없다”라면 그런 선택이 필요하지 않을 수 있다.

[MatrixLimits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/MatrixLimits.lean#L138)은 유한차원에서 극한 행렬 A₀가 injective이면, 성분별로 A₀에 수렴하는 행렬들도 eventually injective임을 얻는다. 개념적으로 A₀의 왼쪽 역행렬 L을 골라 `LA₀ = I`를 만들고, `LA(t)`의 determinant가 1에 수렴함을 이용한다. 충분히 가까우면 determinant가 0이 아니므로 A(t)의 kernel은 0이다. A 자체가 직사각형이어도 이 전략을 쓸 수 있다.

그러면 “eventually 비영 kernel이 존재한다”는 기하학적 구성과 곧바로 모순이다. 비영 벡터를 매개변수에 대해 동시에 고르고 정규화하고 수렴시킬 필요가 없다. 이는 최종 모순에 필요한 정보만 인터페이스로 요구하는 좋은 사례다.

단, 필터에는 `[NeBot l]`이 필요하다. bottom filter에서는 every proposition이 eventually 성립하므로, 서로 반대인 eventually 명제만으로 실제 모순이 나오지 않는다. [모순 정리](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/MatrixLimits.lean#L153)의 이 조건은 장식이 아니라 비공허성 보장이다.

**리팩터링 교훈:** 목표가 존재·비존재의 충돌이면 중간 데이터에 연속성·유일성 같은 더 강한 구조를 불필요하게 부여하고 있지 않은지 살펴본다. 그렇다고 이미 필요한 가정을 자동으로 지워도 되는 것은 아니다. 실제 사용처를 따라가야 한다.

## 10. 첫 실습으로 좋은 부분: 보간

[Interpolation.lean의 ordered rows 보간](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/PlaneCurves/Interpolation.lean#L181)은 큰 기하학보다 진입하기 쉽다. 여러 가로줄의 점들에서 원하는 값을 갖는 2변수 다항식을 만든다고 생각하자.

앞의 n개 줄에서 이미 맞는 다항식 P가 있다. 새 줄 y=Kₙ에서 부족한 값을 x에 대한 다항식 q(x)로 맞춘다. 다음 보정항의 모양을 이용한다.

```text
q(x) × ∏(y − Kᵢ)        [i는 앞의 줄들]
```

앞의 줄에서는 곱 안에 0이 있어 기존 값을 건드리지 않는다. 새 줄에서는 Kₙ과 앞의 Kᵢ가 다르므로 그 곱이 0이 아니어서 부족분을 조정할 수 있다. 이것이 “이전 조건을 유지하며 새 조건을 맞춘다”는 귀납 불변식이다. 실제 Lean 증명은 q를 적절히 정규화하고, 결과가 지정된 monomial space 안에 남는다는 차수 조건까지 확인한다.

공부 순서는 1변수 Lagrange 보간 → 두 줄 보정 → n줄 귀납 → 허용 monomial 범위다. 처음부터 tactic을 줄이지 말고, 보정항이 옛 조건에서 왜 사라지는지를 직접 계산해 보자.

## 11. 실제 refactoring에서는 무엇을 가져올까

이 저장소는 리팩터링 전후 벤치마크를 제공하는 사례가 아니라 큰 수학 개발의 구조 사례다. 따라서 여기서 “이 tactic이 더 빠르다”거나 “이 구조가 Arena 점수를 올린다”는 결론은 얻지 못한다.

가져올 수 있는 것은 다음 작업 방식이다.

- 같은 변환을 반복한다면 차수·multiplicity·비영성을 함께 전달하는 bridge를 찾거나 만든다.
- 구체적인 기하학 구성과 추상적인 선형대수 모순의 경계를 먼저 파악한다.
- 후보가 명제, 정의, 비공허성, 주변 attributes를 유지하는지 확인한다.
- 최종 proof body가 짧아졌다면 이동한 helper도 따로 기록한다.
- 변경 후 같은 pinned 환경에서 대상과 직접 사용처를 검증한다.
- elaboration 비용, 소스 길이, 버전 호환성은 서로 다른 결과로 보고한다.

특히 검토 중 발견한 bridge 자체를 바꿀 때는 원래 방향 두 개와 비영성 보존을 다시 확인해야 한다. 단순 `simp` 정리의 방향을 바꾸는 것도 downstream 단순화의 동작과 비용에 영향을 줄 수 있다.

## 12. `sorry`와 공리를 읽는 방법

[Comparator challenge](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Nagata.lean)는 비교 대상 명제를 선언하기 위해 세 개의 `sorry` 자리를 둔다. 구현 소스의 미완성 증명과 역할이 다르다. 저장소 전체를 검색해서 숫자만 세면 이 차이를 잃는다. 그렇다고 challenge에 있다는 이유로 모든 `sorry`를 무시해서도 안 된다. 구현 최종 정리가 그 placeholder를 의존하지 않는지 실제 proof term 검사로 확인해야 한다.

[설정 JSON](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Nagata.json)은 다음 세 선언을 비교 대상으로 지정한다.

1. `OAI.Nagata.Workers.W30.exists_positive_degree_equation_of_homogeneous_cycle`
2. `OAI.Nagata.nagata_conjecture`
3. `OAI.Nagata.nagata_conjecture_coordinates`

허용 공리는 `propext`, `Quot.sound`, `Classical.choice`다. 이것은 실제 결과 목록이 아니라 허용 정책이다. 실제 목록은 구현을 빌드하고 `#print axioms`로 확인해야 한다. `enable_nanoda`는 false이므로 별도의 kernel 검사까지 실행되었다는 근거로 읽을 수 없다. Comparator 설정 파일이 있다는 사실과 Comparator가 성공했다는 사실도 다르다.

이 구분은 Arena에도 유용하다. 목표 정리의 `sorryAx` 의존성과 다른 선언의 기존 경고를 구별하고, 검증 로그·공리 목록·측정 범위를 결과에 붙인다.

## 13. 스킬에 반영한 변경과 반영하지 않은 것

기존 `lean-refactor`는 이미 명제 보존, 환경 고정, 빌드, 공리 비교, 길이와 비용의 분리를 다뤘다. 이번에는 큰 개발에서 반복되는 검토 항목을 보완했다.

| 추가 항목 | 이 사례에서의 이유 | 적용 시점 |
|---|---|---|
| 양화사·비공허성 확인 | 공통 예외 집합, 공통 여집합, NeBot | 정의/인터페이스 변경 또는 큰 형식화 검토 |
| 표현의 실제 데이터 확인 | 중복 성분을 포함한 cycle과 방정식 | 표현 전환 refactor |
| bridge와 가정 해소 추적 | 조건부 source construction이 실제로 조립되는가 | 큰 증명의 경계 검토 |
| 코드 범위 구분 | 최종 한 줄과 117개 import 모듈 | 길이·비용 결과 보고 |
| artifact 역할과 증거 수준 구분 | challenge sorry, permitted axioms, checker 설정 | 검증 결과 보고 |

상세 기준은 [research-formalization.md](../../../../skills/lean-refactor/references/research-formalization.md)에 두고, [SKILL.md](../../../../skills/lean-refactor/SKILL.md)에는 필요한 때 그 문서를 읽도록 연결했다. 평범한 tactic 정리에 저장소 전체 감사를 강제하지 않는다. theta 함수, cubic 구성, 특정 namespace나 tactic 순서는 범용 규칙으로 넣지 않았다.

## 14. 혼자 공부할 때의 읽기 순서

**1회차 — 문제와 계약.** `Configuration.lean`의 FullNagata, `Nagata.lean`의 최종 선언, `FullTarget.lean`의 ordinary 버전을 읽는다. “무엇을 모든 것으로 고르고 무엇을 먼저 존재시켰는가?”를 종이에 적는다. √r 직관과 실제 정리 사이의 빈틈도 적는다.

**2회차 — 데이터.** `IdealCycles`, `EffectiveCurves`, `CycleMultiplicity`를 읽는다. y와 y² 예제로 차수, cycle 가중치, multiplicity가 어떻게 달라지는지 확인한다. 방정식 선택이 달라도 불변인 값과 선택에 의존하는 데이터를 구별한다.

**3회차 — 선형대수.** `MatrixLimits.lean`의 `basisJetMatrix_mulVec_repr`, `injective_of_basisJetMatrix`, 극한 injectivity 정리를 읽는다. basis에서 좌표를 바꾼다고 실제 선형사상이 바뀌지 않는다는 점과 직사각형 행렬에서 왼쪽 역행렬을 쓰는 이유를 이해한다.

**4회차 — 보간.** `Interpolation.lean`에서 두 줄의 예제를 먼저 손으로 푼다. 보정항이 이미 맞춘 값들을 왜 유지하는지, 서로 다른 줄 조건이 어디 쓰이는지 표시한다.

**5회차 — 조립.** `FullTarget → FixedCurveSections → BasisNoncancellation → Nagata`를 왕복한다. 어떤 조건이 인터페이스에만 있고, 어떤 정리가 실제로 그 조건을 제공하는지 표로 만든다.

**6회차 — 고급 분석.** 논문의 cubic/충돌 설명과 `ThetaLimits`, `ThetaMatrices`, `ScaledMatrices`를 연결한다. 먼저 입력·출력과 정규화 목적을 파악하고 분석적 추정의 세부로 들어간다. 이 단계가 이번 소스 읽기만으로 모두 검증된 영역은 아니다.

각 회차 뒤에는 문법 요약보다 “이 정리가 없으면 어떤 화살표가 끊기는가?”를 한 문장으로 적으면 좋다.

## 15. 이해 확인 문제와 해설

**Q1. 모든 점이 한 직선 위에 있어도 정리가 성립할까?** 아니다. 직선의 차수는 1이고 각 점 중복도가 1이면 합 r은 √r보다 크다. 그래서 일반성의 예외 조건이 본질적이다.

**Q2. `∀F ∃E`와 `∃E ∀F`는 같은가?** 아니다. 전자는 F마다 다른 예외를 허용한다. 후자는 모든 F에 공통으로 사용할 E를 요구한다. 무한히 많은 F의 예외를 무작정 합치는 것만으로 후자가 증명되지는 않는다.

**Q3. y²를 y로 바꾸면 영점집합이 같으므로 괜찮을까?** 점집합을 묻는 문제라면 같지만, 여기서는 차수와 multiplicity가 모두 달라진다. 반복 성분 가중치를 보존해야 한다.

**Q4. 최종 proof body가 한 줄이면 전체 증명도 작다고 할 수 있을까?** helper를 호출하는 인터페이스가 짧다는 뜻이다. 소스 전체, 실제 의존 proof term, elaboration 비용은 따로 봐야 한다.

**Q5. 모든 가까운 t에 비영 kernel이 있다는 가정에서 v(t)를 연속으로 골라야 할까?** 극한 행렬의 injectivity가 가까운 행렬로 전달되면 그럴 필요가 없다. 각 t의 존재와 eventually injective를 충돌시키면 된다. 필터가 NeBot이라는 전제는 필요하다.

**Q6. JSON의 permitted_axioms 세 개가 최종 공리 목록인가?** 아니다. 허용 목록이다. 실제 출력은 해당 toolchain으로 빌드한 구현 정리에 대해 검사해야 한다.

## 16. 아직 남은 검증과 재현 계획

이 checkout에는 요구하는 Lean `v4.34.1`과 대응 의존성이 준비되어 있지 않다. 다른 로컬 버전을 대신 사용하지 않았다. Mathlib pin은 `d13f23b723b8a846827a245b89c10fc7d3f11612`다. `comparator`, `landrun`, `lean4export`도 로컬 PATH에서 찾지 못했다.

아래는 **향후 실행 계획**이며 이번에 통과한 명령 목록이 아니다.

```bash
# 선택 checkout 위치의 lean 디렉터리에서 실행
cd /Users/sungwoo/lean_project/external-reviews/openai-math/lean
elan show
# v4.34.1 및 manifest의 pinned 의존성을 먼저 준비한다.
# setup이 manifest를 변경한다면 revision 차이를 확인한다.
lake exe cache get
lake build OAI.AlgebraicGeometry.PlaneCurves.Nagata
```

그 뒤 임시 검사 파일에서 구현 모듈을 import하고 세 대상 선언에 `#print axioms`를 실행한다. 주변 모듈의 경고와 대상의 `sorryAx` 의존성을 구별한다. Comparator와 보조 실행 도구를 저장소 지침대로 준비한 뒤 `lake env comparator ComparatorChallenges/Nagata.json`을 실행해 실제 로그를 보관한다. 별도 kernel 검증을 수행했다면 도구·버전·명령·결과도 별도로 기록한다. 저장소의 README 예제에 다른 문제명이 등장하므로 Nagata 설정 경로를 사용해야 한다.

소스 검색만 재현하려면 workspace 루트에서 다음 명령을 쓴다.

```bash
python3 LeanAgent/docs/research/lean-mathlib/nagata-study/scan_sources.py \
  external-reviews/openai-math \
  --output /tmp/nagata-source-audit.json
```

향후 정리의 명제와 관련 정의가 comparator 기준과 일치하는지, 실제 공리 목록이 허용 정책을 만족하는지, 논문의 중요한 해석 연결이 정확한지를 더 검증해야 한다. 현재 자료의 가장 확실한 가치는 그 검증에 필요한 경계와 질문을 드러내고, 표현을 바꾸면서 의미를 보존하는 개발 방식을 구체적인 소스로 공부할 수 있게 했다는 점이다.
