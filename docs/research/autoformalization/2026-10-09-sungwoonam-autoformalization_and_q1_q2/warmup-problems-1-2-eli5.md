# Warm-up 1·2 ELI5 — 무엇을 증명하는 문제인가?

작성일: 2026-10-06 · 설명 보완: 2026-10-09 · 읽는 순서: Strata → AST 순회 → 문제 뜻 → 증명 → 리팩터링 결과

## 먼저: Strata는 무엇이고, 왜 이런 문제를 풀까?

[Strata](https://github.com/strata-org/Strata)는 프로그램의 문법과 의미를 정의하고 분석·검증 도구를 만드는 Lean 기반 프레임워크다. 분석하기 쉽도록 프로그램을 다른 형태로 바꾸는 과정이 있다. 변환 코드가 실수하면 분석 결과도 믿기 어려우므로, 변환이 필요한 성질을 지키는지도 증명한다. Lean은 이 증명을 기계적으로 검사하는 도구다.

이번 두 정리는 함수 호출을 계약에 기반한 기본 명령으로 바꾸는 과정에서 쓰이는 **변수 이름 관리의 보조정리**다. 변환 전체의 정확성을 이 두 정리만으로 증명하는 것은 아니다.

Warm-up에서는 이미 있는 명제와 증명을 받아, **명제를 유지하면서 증명 코드의 구조를 개선**한다. 이 두 사례는 식의 종류별 경우 분석과 목록 포함 추론이 반복되어, 공통 절차와 귀납 대상 선택을 연습하기 좋다. 이는 학습 관점의 설명이며 출제자의 구체적인 선정 의도를 확인했다는 뜻은 아니다. 알고리즘 자체의 실행 속도를 개선하는 과제와도 구분해야 한다.

### AST와 순회부터 이해하기

AST는 Abstract Syntax Tree(추상 구문 트리)의 줄임말이다. 식을 글자 나열 대신 “어떤 연산에 어떤 식이 들어가는가”라는 나무 구조로 표현한다. 다음은 설명을 위해 단순화한 나무다.

```text
x = old(y) + z

=
├─ x
└─ +
   ├─ old
   │  └─ y
   └─ z
```

**순회**는 이 노드들을 일정한 규칙으로 방문하는 것이다. 위에서 시작해 왼쪽부터 방문하면 `= → x → + → old → y → z` 순서다. 변수 노드에서만 이름을 모으면 `[x, y, z]`를 얻는다. 식의 값을 계산하는 것은 아니다. 연산자 `old`와 `+`는 변수 이름에 넣지 않는다. 실제 Strata에서는 `old(y)`가 `app (op old) (fvar y)` 같은 구조다. `app`은 함수 적용, `op`는 연산자, `fvar`는 자유 변수다.

같은 나무를 순회해도 목적에 따라 작업이 다르다. `getVars`는 모든 자유 변수 이름을 모으고, `extractOldExprVars`는 old 안의 변수 이름을 모으며, `substOld`는 일치하는 old 부분을 새 식으로 바꾼다.

**구조 귀납**은 순회 함수의 성질을 증명하는 방법이다. 작은 식들에서 성질이 성립한다고 가정하고, 그 식들을 조립한 큰 식에서도 성립함을 보인다. 순회는 데이터를 처리하는 실행이고 귀납은 그 처리의 성질에 대한 증명이다. [HTML의 순회 데모](./warmup-problems-1-2.html#ast)에서 이름이 모이는 과정을 따라갈 수 있다.

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

**보장하지 않는 것:** h1이 다른 변수와 충돌하지 않는 새 이름인지, 실제로 올바른 호출 전 값을 저장했는지, 변환 전후 식의 값이 같은지는 이 명제에 없다. 또 `old(y) + y`에서는 old 부분만 바뀌고 바깥의 y는 그대로다.

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

## 5. 새 증명: 목록 결합 성질을 한 번만 증명하기

1번은 AST에 귀납한다. combine은 두 부분 식의 결과가 각각 “원래 이름 + h1” 안에 있으면 합친 결과도 “전체 원래 이름 + h1” 안에 있음을 보인다. 상수·변수는 직접 처리하고, 여러 부분 식을 가진 노드는 combine을 재사용한다. old 적용은 치환 여부에 따라 나눈다.

```lean
  have combine {a b c d : List CoreIdent}
      (ha : a.Subset (c ++ [h1])) (hb : b.Subset (d ++ [h1])) :
      (a ++ b).Subset ((c ++ d) ++ [h1]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp (ha hx) with hx | hx
      · exact List.mem_append_left _ (List.mem_append_left _ hx)
      · exact List.mem_append_right _ hx
    · rcases List.mem_append.mp (hb hx) with hx | hx
      · exact List.mem_append_left _ (List.mem_append_right _ hx)
      · exact List.mem_append_right _ hx
  induction post with
  | const | bvar | op => exact List.Subset.empty
  | fvar => exact List.subset_append_left _ _
  | abs _ _ _ ih => exact ih
  | quant _ _ _ _ _ ih1 ih2 => exact combine ih1 ih2
  | ite _ _ _ _ ih1 ih2 ih3 => exact combine (combine ih1 ih2) ih3
  | eq _ _ _ ih1 ih2 => exact combine ih1 ih2
  | app _ fn arg ihfn iharg =>
    unfold substOld
    split
    · split <;> simp [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars, List.Subset]
    · exact combine ihfn iharg
```

2번은 정규화 증거에 귀납한다. combine은 두 포함 관계를 합친다. old(변수)에서는 이름이 이미 원래 식에 있고, 잘못된 old 인수는 정규화 증거와 모순이다. 일반 적용에서는 귀납 가설 둘을 합친다.

```lean
  have combine {a b c d : List CoreIdent}
      (ha : a.Subset c) (hb : b.Subset d) : (a ++ b).Subset (c ++ d) :=
    fun _ hx => (List.mem_append.mp hx).elim
      (fun hx => List.mem_append_left _ (ha hx))
      (fun hx => List.mem_append_right _ (hb hx))
  intro h
  induction h with
  | const | op | bvar | fvar => exact List.Subset.empty
  | abs _ ih => exact ih
  | quant _ _ ih1 ih2 => exact combine ih1 ih2
  | ite _ _ _ ih1 ih2 ih3 => exact combine (combine ih1 ih2) ih3
  | eq _ _ ih1 ih2 => exact combine ih1 ih2
  | app hfn harg hold ihfn iharg =>
    unfold extractOldExprVars
    split
    · exact fun _ hx => hx
    · next hfalse =>
      cases hold .oldPred
      exact False.elim (hfalse _ _ _ rfl)
    · exact combine ihfn iharg
```

## 6. 코드를 사람 말로 읽기

| 코드 | 의미 |
| --- | --- |
| `have combine` | 재사용할 목록 결합 성질을 먼저 증명 |
| `induction` | 작은 식/증거에서 성립하면 조립한 경우에도 성립함을 확인 |
| `rcases` | 증거의 경우를 나누기 |
| `List.mem_append.mp` | 합친 목록의 이름은 왼쪽 또는 오른쪽에 있음 |
| `List.mem_append_left/right` | 부분 목록의 이름을 합친 목록으로 옮기기 |
| `exact` | 현재 목표에 맞는 증거를 제출 |
| `hold .oldPred` | old의 인수가 자유 변수라는 정규화 조건을 적용 |
| `False.elim` | 모순된 가정으로 불가능한 분기를 제외 |

## 7. 검증과 측정 결과

2026-10-09에 Lean v4.26.0과 Strata revision `451e5f047bafa010d178856db76c00029bfa4d7f`에서 모듈 빌드, 명제 동일성, 공리 의존성을 확인했다.

| 항목 | 1번 원본 → 새 증명 | 2번 원본 → 새 증명 |
| --- | --- | --- |
| 증명 몸체 비어 있지 않은 줄 | 91 → 23 | 77 → 20 |
| 공백 제외 문자 | 1,668 → 769 | 1,172 → 533 |
| heartbeat 중앙값 | 5,207.667 → 1,105.482 | 2,612.070 → 461.131 |
| 공리 | [propext, Quot.sound] 동일 | [propext, Quot.sound] 동일 |

크기에는 combine 보조 증명도 포함한다. Heartbeat는 Lean의 작업량 계수이며 실행 시간은 아니다. 같은 선언 이름으로 각각 새 Lean 프로세스에서 3회 측정했다. import 이후 동기 선언 elaboration·검사의 내부 계수를 1,000으로 나눈 값이다. 공식 Arena 점수와 다른 버전의 호환성 결과는 별개다.

[새 증명 파일](./artifacts/warmup-1-2/improved_proofs.lean) · [측정 원자료](./artifacts/warmup-1-2/heartbeat-2026-10-09/measurements.json) · [재현 방법](./artifacts/warmup-1-2/README.md)

## 8. 내가 이해했는지 확인하기

1. `x = old(y) + z`에서 `old(y)`를 `saved_y`로 바꾸면 허용 변수 목록에 무엇을 추가해야 할까?
2. `old(y) + old(y)`의 추출 목록 `[y, y]`가 전체 변수 목록의 subset이어도 괜찮을까?
3. 2번에서 `induction h`가 부분 식의 정규화 증거를 얻기 좋은 이유는 무엇일까?
4. 증명이 5줄이면 원본보다 heartbeat도 적다고 결론낼 수 있을까?

답: 1. `saved_y`. 2. 그렇다. subset은 중복 횟수를 제한하지 않는다. 3. 정규화 증거의 생성자가 부분 식의 증거를 갖고 있기 때문이다. 4. 측정 전에는 알 수 없다.

다음으로 [논문 추천과 실험 지도](../../research/autoformalization/refactor-arena-study-guide.md)를 읽자.
