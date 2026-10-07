# Warm-up 1·2 ELI5 — 무엇을 증명하는 문제인가?

작성일: 2026-10-06 · 읽는 순서: 문제 뜻 → 예제 → 증명의 원리 → 리팩터링 코멘트

## 1. 배경: “아까 값”을 기억하는 프로그램

통장에 10원이 있고 함수가 3원을 더한다고 하자. 함수가 끝난 뒤 잔액은 13원이고, 시작할 때 잔액은 10원이다. 프로그램의 계약에서 `old(balance)`는 **함수 호출 전 balance 값**을 뜻한다.

예를 들어 함수 실행 후 만족해야 하는 조건, 즉 `post`를 이렇게 쓸 수 있다.

```text
balance = old(balance) + 3
```

Strata의 call elimination은 함수 호출을 더 기본적인 명령으로 바꾸는 변환이다. 이때 호출 전 값을 임시 변수에 저장하고, 계약의 `old(balance)`를 그 임시 변수로 바꾸는 방식이 필요하다. 여기의 두 정리는 이 변환 과정에서 **변수 목록을 안전하게 관리할 수 있는지** 확인하는 부품이다. 두 정리만으로 프로그램 전체의 의미 보존을 증명하는 것은 아니다.

## 2. 읽기 전에 알아둘 다섯 단어

| 코드 | 쉬운 뜻 |
| --- | --- |
| `post` | 실행 후 지켜야 하는 조건식 |
| `getVars e` | 식에 쓰인 자유 변수 이름을 모은 목록 |
| `A.Subset B` | A에 있는 이름은 모두 B에도 있다 |
| `++` | 목록 두 개 이어 붙이기 |
| `NormalizedOldExpr e` | old가 정해진 모양으로 쓰였다는 증거 |

`getVars`는 값을 계산하지 않는다. `x + y`에서 x와 y라는 **이름**을 수집한다. 목록에는 같은 이름이 반복될 수 있다. 여기의 subset은 등장 횟수나 순서를 비교하지 않고 소속 여부만 본다.

표현식은 블록으로 조립한 나무(AST)다. 변수·상수가 잎이고 함수 적용·조건문·등식 등이 가지다. Lean에서 `old(x)`는 “old 연산자를 x에 적용한 노드”로 표현된다. `old` 자체는 연산자라 `getVars`에 변수 이름으로 들어가지 않는다. 아래 예제들은 이해를 위한 표기이며 그대로 붙여넣는 Lean 코드는 아니다.

## 3. 문제 1: 치환해도 예상 못 한 이름이 생기지 않는다

정리 이름: `CallElimCorrect.substOldPostSubset`

> **식에서 `old(h2)`를 변수 `h1`으로 바꿨다면, 결과 식의 변수는 원래 있던 변수 또는 `h1`이다.**

```text
getVars(substOld h2 (변수 h1) post) ⊆ getVars(post) ++ [h1]
```

통장 예제로 이름을 바꾸면:

```text
원래 식:     balance = old(balance) + fee
치환 대상:   h2 = balance
저장 변수:   h1 = saved_balance
변경된 식:   balance = saved_balance + fee

원래 이름:   [balance, balance, fee]
결과 이름:   [balance, saved_balance, fee]
허용 이름:   [balance, balance, fee, saved_balance]
```

결과에 `mystery`라는 새 이름이 갑자기 나타나지 않는다는 보장이다. `[h1]`을 붙이는 이유는 치환으로 h1이 새로 등장할 수 있기 때문이다. 치환할 old가 없으면 아무 변화가 없어도 된다. 그래서 “정확히 이 목록과 같다”가 아니라 “이 목록 안에 포함된다”이다.

`h2`와 `h1`은 이름이고, `m`과 `ty`는 해당 변수 표현식의 메타데이터와 타입이다. 이 정리가 말하는 것은 자유 변수 이름의 범위다.

**어떻게 증명할까?** 나무를 가장 작은 블록부터 확인한다. 상수면 변수 없음, 일반 변수면 원래 이름 그대로, `old(h2)`면 h1로 교체된다. 큰 식은 작은 식들의 변수 목록을 합치므로, 작은 식마다 성질이 맞으면 큰 식도 맞는다. 이것이 `induction post`다. 이 정리에는 `NormalizedOldExpr post` 가정이 없다.

## 4. 문제 2: old에서 뽑은 이름은 원래 식에도 있다

정리 이름: `CallElimCorrect.extractedOldExprInVars`

> **old가 규칙에 맞게 쓰였다면, old 안에서 추출한 변수 이름은 모두 원래 식의 변수 목록에 있다.**

```text
NormalizedOldExpr post → extractOldExprVars post ⊆ getVars post
```

예를 보자.

```text
식:                  x = old(y) + old(z) + w
old에서 추출한 이름: [y, z]
전체 자유 변수 이름: [x, y, z, w]
```

old 상자 속 이름을 모아도, 식에 없는 이름을 만들어 내지는 않는다는 말이다.

**왜 정규화가 필요한가?** 추출 함수는 `old(변수)` 모양을 기대한다. `old(x + y)`처럼 변수 하나가 아닌 식을 직접 받는 경우는 추출 함수의 `panic!` 분기에 해당한다. 따라서 정규화 증거는 이 분기를 제외하는 데 중요하다. “괄호를 예쁘게 정리했다” 정도의 뜻이 아니다.

정확한 규칙은 application 생성자의 `(IsOldPred fn → IsFvar e)`다. old 연산자를 실제로 적용했다면 그 인수가 자유 변수여야 한다. 적용되지 않은 old 연산자 자체는 허용하므로, 모든 AST가 단순히 old 상자로만 구성된다는 설명도 정확하지 않다.

통장 예제에서는 `extractOldExprVars`가 `[balance]`를 돌려준다. 이는 어떤 호출 전 값을 저장해야 하는지 알아내는 데 쓰일 수 있다. 실제로 인접 정리 `extractedOldVarsInVars`는 정규화 후 이 정리를 적용한다.

## 5. 리팩터링의 핵심: 같은 검사표를 반복하지 않기

### 1번 — 반복 작업을 하나의 절차로 묶었다

원본은 표현식 종류마다 거의 같은 subset 추론을 손으로 적었다. 새 증명은 “나무 분해 → 치환 정의 펼치기 → 필요한 분기 → 변수 목록 단순화 → 목록별 subset → 마무리”를 모든 경우에 적용한다.

```lean
induction post <;> unfold substOld <;> (try split <;> try split) <;>
  simp_all [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] <;>
  (repeat' apply List.Subset.app) <;> (try (apply List.Subset.trans; assumption)) <;>
  simp +contextual [List.Subset, or_imp]
```

ELI5 코멘트: **종류별로 같은 검사표를 아홉 번 쓰는 대신, 공통 검사표를 만들어 각 종류에 돌렸다.** 논리를 생략한 것이 아니라 Lean이 반복 부분을 실행하고 증명 항을 확인한다.

### 2번 — 검사할 대상을 더 잘 골랐다

원본은 `post`라는 나무 자체에 귀납한 뒤, 매번 정규화 증거를 다시 꺼냈다. 새 증명은 `h : NormalizedOldExpr post`라는 **규칙을 지켰다는 증거의 구성 과정**에 귀납한다.

```lean
intro h
induction h <;> unfold extractOldExprVars <;> (try split) <;>
  simp_all [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars] <;>
  (repeat' apply List.Subset.app) <;> (try (apply List.Subset.trans; assumption)) <;>
  simp +contextual [List.Subset]
```

ELI5 코멘트: **모든 장난감을 꺼내 규칙 위반을 검사하는 대신, 규칙에 맞게 조립했다는 설명서를 따라 확인한다.** 부분 식의 정규화 증거와 귀납 가설을 함께 얻어 처리가 자연스럽다. 다만 `app` 안의 조건 분기는 여전히 남고 단순화로 처리한다.

원본의 `induction post`는 올바른 증명이다. “잘못된 귀납”보다는 **이 문제에서는 덜 직접적이고 반복이 많은 귀납**이라고 설명하는 편이 맞다.

## 6. tactic을 사람 말로 읽기

| 코드 | 의미 |
| --- | --- |
| `intro h` | 정규화됐다는 가정을 h라는 이름으로 받기 |
| `induction` | 작은 부품에서 성립하면 조립한 식에서도 성립하는지 확인 |
| `<;>` | 앞 단계에서 생긴 모든 목표에 다음 절차 적용 |
| `unfold` | 함수 이름을 실제 정의로 펼치기 |
| `split` | match/조건의 경우 나누기 |
| `try` | 해당 절차가 적용되지 않아도 다음 단계로 진행 |
| `simp_all` | 목표와 가설을 알려진 규칙으로 함께 정리 |
| `List.Subset.app` | 합친 목록의 subset을 두 목록의 subset으로 분해 |
| `List.Subset.trans` | A ⊆ B와 B ⊆ C를 연결해 A ⊆ C |
| `assumption` | 필요한 증거를 현재 가설에서 찾기 |
| `repeat'` | 적용할 수 있는 목표에 같은 tactic 반복 |
| `simp +contextual` | 문맥의 가정을 활용해 소속 조건을 정리 |

`try`는 실패를 무시할 수 있지만, 마지막에 미완성 목표가 있으면 Lean은 증명을 거부한다. 자동화가 많다고 검증 기준이 느슨해지지는 않는다.

## 7. 결과를 어떻게 코멘트하면 좋을까?

> 1번은 반복적인 AST 경우 분석과 목록 포함 추론을 공통 tactic 절차로 묶었다. 2번은 정규화 증거에 귀납하여 가정을 뒤늦게 분해하던 중복을 줄였다. 두 정리의 명제는 유지되고, 원본과 후보의 공리 목록은 모두 `[propext, Quot.sound]`로 확인됐다. 소스 크기는 크게 줄었지만 heartbeat 개선과 버전 호환성은 별도 측정이 필요하다.

| 항목 | 1번 | 2번 | 근거 |
| --- | --- | --- | --- |
| 증명 몸체 비어 있지 않은 줄 | 91 → 4 | 77 → 5 | JSONL 원본 및 현재 소스 재계산 |
| 공백 제외 문자 | 1,668 → 237 | 1,172 → 232 | 같은 범위로 재계산 |
| 공리 목록 | 원본/후보 동일 | 원본/후보 동일 | Lean `#print axioms` |
| v4.26.0 검증 | 통과 | 통과 | 모듈 빌드 및 원본 재검증 |
| heartbeat/다른 버전 | 미측정 | 미측정 | 현재 자료에 측정 로그 없음 |

1번 몸체는 빈 줄을 포함하면 92줄이다. “91줄”은 비어 있지 않은 줄을 센 값이다. 기존 보고서의 Lean token과 tactic 호출 수는 산정 도구가 남아 있지 않아 이번에 재검증하지 않았으며 공식 점수로 취급하지 않는다. JSONL의 1번 `proof_length`는 313으로 기존 표의 312와도 차이가 있다.

빌드는 성공하지만 다른 정리에 기존 `sorry` 경고가 있다. 두 대상 정리 자체의 공리 검사에는 `sorryAx`가 없다. `[propext, Quot.sound]`가 같다는 것은 공리 의존성을 보존했다는 확인이며, 파일 전체가 공리 없는 증명이라는 뜻은 아니다.

**장점:** 반복 감소, 논리적 구조가 선명해짐, 위치 기반 변수 이름 변경 감소.

**남은 평가:** 자동화는 읽을 줄 수를 줄여도 실행 비용을 늘릴 수 있다. `simp_all`은 가설과 simp 규칙 변화에 영향을 받으므로 다른 버전에서도 더 견고하다는 결론은 아직 낼 수 없다. 초보자에게는 짧은 코드 옆에 지금 같은 설명을 남기는 것이 좋다.

## 8. 내가 이해했는지 확인하기

1. `x = old(y) + z`에서 `old(y)`를 `saved_y`로 바꾸면 허용 변수 목록에 무엇을 추가해야 할까?
2. `old(y) + old(y)`의 추출 목록 `[y, y]`가 전체 변수 목록의 subset이어도 괜찮을까?
3. 2번에서 `induction h`가 부분 식의 정규화 증거를 얻기 좋은 이유는 무엇일까?
4. 증명이 5줄이면 원본보다 heartbeat도 적다고 결론낼 수 있을까?

답: 1. `saved_y`. 2. 그렇다. subset은 중복 횟수를 제한하지 않는다. 3. 정규화 증거의 생성자가 부분 식의 증거를 갖고 있기 때문이다. 4. 측정 전에는 알 수 없다.

다음으로 [논문 추천과 실험 지도](../../research/autoformalization/refactor-arena-study-guide.md)를 읽자.
