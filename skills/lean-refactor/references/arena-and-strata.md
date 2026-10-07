# Arena 평가와 현재 Strata 사례

Arena 제출·평가 또는 이 워크스페이스의 warm-up 1·2를 작업할 때 읽는다. 아래는 프로젝트를 찾는 단서와 2026-10-06 검증 기록이다. 새로운 실행의 결과나 현재 공식 규칙을 대신하지 않는다.

## Arena

공식 안내: [Arena](https://leanrefactor.github.io/), [워크숍](https://vericodegen.github.io/). 제공된 benchmark의 `statement`, `src`, `file_path`, `version_info`와 실제 제출 규칙에서 실행 환경·지표·예산을 확인한다. 규칙은 변할 수 있으므로 이 파일에 고정된 날짜·점수 공식·예산을 복사하지 않는다.

논문 아이디어와 공식 대회 요구를 구분한다. 대회에서 요구하는 명제 보존, 허용 패턴, 평가 도구와 버전 목록은 실제 안내를 따른다. “공리 목록 동일”만으로 공식 유효성 전체를 확인했다고 표현하지 않는다.

후보별 결과를 비교할 때:

| 항목 | 기록 기준 |
| --- | --- |
| correctness | 동일한 명제·문맥과 대상 환경에서 Lean 검증 |
| axioms | 원본/후보의 `#print axioms` 결과 |
| size | 공식 도구의 proof source token; 없으면 보조 지표임을 명시 |
| elaboration cost | 공식 heartbeat 측정 또는 fresh 실행의 정의된 지표 |
| compatibility | 지정 버전별 같은 proof body의 결과 |
| API spend | 해당 run의 모든 호출, 재시도·폐기 후보 포함 |

## 이 워크스페이스에서 자료 찾기

`lean_project`의 위치는 고정하지 말고 실제 checkout에서 찾는다. 루트 아래:

- `refactor_arena/benchmark_data_warmup.jsonl`: 원본 문제와 버전 정보.
- `refactor_arena/strata`: Strata checkout.
- `refactor_arena/strata/Strata/Languages/Core/OldExpressions.lean`: `substOld`, `extractOldExprVars`, `NormalizedOldExpr`.
- `refactor_arena/strata/Strata/DL/Lambda/LExpr.lean`: `LExpr.getVars`.
- `refactor_arena/strata/Strata/Transform/CallElimCorrect.lean`: 대상 두 정리와 사용처.
- `refactor_arena/verify_warmup_1_2.lean`: 원본 재검증과 공리 비교용 파일.
- `refactor_arena/warmup_1_2_verification.json`: 이전 결과의 범위와 미측정 항목.
- `LeanAgent/docs/meetings/2026-10-11-week2/warmup-problems-1-2-eli5.md`: 문제 이해 자료.
- `LeanAgent/docs/research/autoformalization/refactor-arena-study-guide.md`: 논문 연결과 비교 실험 제안.

이전 검증은 HEAD `451e5f047bafa010d178856db76c00029bfa4d7f`에 로컬 proof 수정이 있는 상태, Lean `v4.26.0`이었다. 재현 전 현재 git 상태와 toolchain을 다시 확인한다.

Strata checkout 안에서 사용한 명령:

```sh
lake build Strata.Transform.CallElimCorrect
lake env lean ../verify_warmup_1_2.lean
```

## 사례에서 배운 점

1. `substOldPostSubset`: `old(h2)`를 자유 변수 h1으로 치환한 결과의 변수는 원래 변수 또는 h1이다. 명제는 정규화 가정을 요구하지 않는다. 구조 귀납과 반복 subset 추론의 공통 처리가 핵심이었다.
2. `extractedOldExprInVars`: 정규화된 식에서 old 안의 변수 이름을 추출하면 원래 자유 변수 목록의 subset이다. `NormalizedOldExpr` 증거에 귀납하면 부분 식의 정규화 증거와 귀납 가설을 함께 얻는다. application 조건 분기는 여전히 확인해야 한다.
3. `List.Subset`은 목록의 membership을 비교하며 순서·중복 횟수를 보존한다는 명제가 아니다.
4. 두 원본과 후보의 공리는 모두 `[propext, Quot.sound]`였다. 모듈에는 다른 선언의 기존 `sorry` 경고가 있었다.
5. proof body의 비어 있지 않은 줄은 91→4, 77→5였다. 이 기록에는 공식 token, heartbeat 개선과 다른 버전 호환성 결과가 없다. 기존 HTML 표의 token/tactic 값은 도구가 남아 있지 않아 재검증되지 않았다.

이 결과는 공통 자동화와 귀납 대상 선택을 시도할 근거다. `simp_all`과 특정 tactic 조합의 보편적 효율·견고성을 보장하지 않는다.
