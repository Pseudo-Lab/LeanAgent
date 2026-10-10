# Week 2 — P7·P12 참조 증명 실행과 리팩터링 기록

작성: 손지연 · 검증일: 2026-10-10 (Asia/Seoul) · 공유 예정: 2026-10-11.

이 문서는 완료된 로컬 실행 기록을 정리한 자료다. PR 준비 중 Lean 검증을 새로 실행하지 않았다. [검증 자료 폴더](refactoring-07-12/)에는 최종 로그·결과 JSON과 P12의 실패 로그를 보관한다. 증명 소스·실행 스크립트·의존성 저장소는 기존 로컬 작업 폴더에 있으며 이 PR에는 포함하지 않는다. JSON의 실행 명령은 당시 문제 폴더 기준 상대 경로로 정규화했고, 원본 JSON의 SHA-256을 함께 기록했다.

두 문제의 JSONL `statement`를 유지하면서 `src`를 읽고, 참조 증명과 리팩터링한 증명을 각각 Lean으로 검증했다. 최종 네 번의 검증은 모두 성공했고 대상 정리의 `sorryAx` 의존성은 없다. 참조본과 수정본의 `#check`·`#print axioms` 출력도 문제별로 동일하다.

## 참조 증명 복원과 검증 방식

| 문제 | 항목 이름 | Lean | 라이브러리 커밋 |
| --- | --- | --- | --- |
| P7 | `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress` | `v4.33.0-rc2` | `3aa9d4416c185e0b9faeb72bbd65abe85b95dbcc` |
| P12 | `interleaved_affine_gaps_imply_tensor_gaps` | `v4.31.0` | `c1712f6c496d0aef04f09bae42aec13811b3273f` |

P7은 `Fsub.Typing`만 import하고 namespace·변수를 복원한다. 대상 정리가 이미 들어 있는 `Fsub.Safety`는 import하지 않는다. P12는 `DG25.Basic`을 import하고 `MainResults.lean`에서 대상 정리 앞의 보조정리 문맥을 복원한다. 대상 정리를 포함한 `MainResults` 자체를 import하지 않는다. 따라서 수정본이 참조 정리를 그대로 호출해 증명을 끝내는 구조가 아니다.

당시 검증 세션에는 Lean MCP 도구가 없어 `lake env lean`으로 수정한 파일을 확인했다. 최종 스크립트는 필요한 import 모듈을 `lake build`한 뒤 두 파일을 각각 검사한다. 수정본에도 JSONL의 명제 선언이 그대로 있는지 확인하며, `-DwarningAsError=true`로 대상 파일의 경고를 오류로 처리한다. P12는 원본 환경에 맞춰 `-DautoImplicit=false`도 지정한다.

## 최종 실행 결과

| 문제 | 참조본 | 수정본 | `sorryAx` | 최종 로그 |
| --- | --- | --- | --- | --- |
| [P7](refactoring-07-12/P7/result.json) | PASS, 4.46초 | PASS, 3.52초 | 양쪽 모두 없음 | [참조](refactoring-07-12/P7/reference.log), [수정](refactoring-07-12/P7/refactored.log) |
| [P12](refactoring-07-12/P12/result.json) | PASS, 10.79초 | PASS, 10.61초 | 양쪽 모두 없음 | [참조](refactoring-07-12/P12/reference.log), [수정](refactoring-07-12/P12/refactored.log) |

시간은 최종 실행 1회의 `lake env lean` 경과 시간이며, 앞선 의존성 빌드·다운로드는 제외한다. P12는 복원한 앞부분의 보조정리도 매번 검사한다. 이 수치만으로 실행 속도 개선을 일반화하지 않는다.

네 증명의 공리 목록은 모두 다음과 같다.

```text
[propext, Classical.choice, Quot.sound]
```

## P7 — 귀납적 정의의 분기와 대칭성

### 참조 증명을 읽은 내용

명제는 빈 환경에서 타입을 갖는 항이 값이거나 한 단계 call-by-value 계산할 수 있다는 progress 정리다. `Typing` 유도에 대한 귀납법을 사용한다. 빈 환경을 일반화한 뒤 각 분기에서 다시 복원하며, 부분항에 귀납가정을 적용한다.

함수 적용·타입 적용·합 타입의 경우에는 값의 canonical form을 확인한 뒤 계산 규칙을 선택한다. `inl`과 `inr`는 부분항이 값이면 전체도 값이고, 부분항이 계산하면 전체도 계산한다는 동일한 구조다. `abs`와 `tabs`는 local closure를 얻으면 즉시 값이 된다.

### 수정 시도와 결과

| 시도 | 결과·해결 |
| --- | --- |
| 이동한 P7 실행 스크립트의 데이터 경로 확인 | `ROOT / benchmark_data_warmup.jsonl`이 이전 위치를 가리키고 있었다. `ROOT.parent`로 수정한 뒤 참조본 재검증에 성공했다. |
| 전체 typing 유도와 분기별 유도에 같은 `typed` 이름 사용 | `ih rfl typed`에 부분항이 아닌 전체 항의 typing이 전달되는 타입 불일치가 발생했다. 보존한 전체 유도를 `wholeTyped`로 이름 붙여 해결했다. |
| `inl`·`inr`를 합친 분기로 처리 | `case inl ... \| inr ...`에서 값 생성자와 계산 생성자를 같은 코드로 선택하도록 바꿨다. 검증 성공. |
| `abs`·`tabs`의 local closure 구성 통합 | 각자 `LC.abs`·`LC.tabs`를 구성하던 코드를 `wholeTyped.wf.2.1`로 대체했다. 검증 성공. |
| 함수 적용의 계산 규칙 명시 | `Red.abs`, `Red.appᵣ`, `Red.appₗ`로 세 계산 경로를 직접 표현했다. 부분항의 계산 결과는 `rcases`로 즉시 분해한다. 검증 성공. |

정리 전체는 **83줄 → 49줄**, `grind` 출현은 **19회 → 8회**가 되었다. 줄 수에는 선언·빈 줄·주석을 포함하고 파일의 import 문맥과 검사 명령은 제외했다.

### 남겨 둔 부분

빈 환경 일반화와 전체 typing 유도의 보존은 유지했다. canonical-form 분석과 `let`·`case`의 local closure 조건에는 기존 `grind`를 일부 사용한다. 서로 다른 계산 규칙까지 하나의 큰 자동화 전술로 합치지는 않았다. 최종 증명을 막는 미해결 오류는 없다.

## P12 `interleaved_affine_gaps_imply_tensor_gaps` — ArkLib
- 인덱스·형 변환·확률 부등식 정리

**한 줄 요약:** 기본 코드와 모든 interleaved code에서 affine-line proximity gap이 있으면 임의 차원의 multilinear correlated-agreement gap으로 확장됨을 귀납적으로 보입니다.

### 참조 증명을 읽은 내용

모든 양의 interleaving factor에 대한 affine-line proximity gap을 가정해, 원래 코드의 양의 차원 tensor/multilinear correlated agreement를 증명한다.

귀납의 기저 `ϑ = 1`은 다중선형 결합을 affine-line evaluation으로 바꾸고 `Fin 1 → F`의 균등 샘플링을 `F`의 샘플링으로 바꾸는 단계다. 귀납 단계는 word stack을 두 절반으로 나누고 마지막 무작위 좌표를 먼저 샘플링한다. 좋은 매개변수 집합 `R*`의 확률 하한, 그 집합에서의 귀납가정, interleaved-code gap을 연결한 뒤 두 절반의 correlated agreement를 합친다.

원본에는 `Fin.snoc` 복원에 대한 인덱스 분기, 여러 `ϑ` 별칭, 반복되는 interleaved-word 형 주석, `ℕ`·`ℝ≥0`·`ENNReal` 사이의 변환이 섞여 있었다. 특히 `h_R_star_card_gt_eps`는 길게 증명한 뒤 **후속 논증에서 사용하지 않았다**. 실제 마무리는 `R*`의 확률 하한과 확률 단조성만 사용한다.

### 최종 리팩터링

| 구성 | 역할 |
| --- | --- |
| `tensor_success_split` | 원래 성공 사건을 재귀적인 affine 결합 사건과 점별로 동일시한 뒤, 기존 균등 샘플링 분할 정리를 적용한다. `Fin.snoc` 재구성과 수동 인덱스 case split이 사라진다. |
| `tensor_gap_one` | singleton 샘플링 변환과 두 행의 표현 변환을 기저 단계 안에 모은다. |
| `tensor_gap_succ` | `R*`의 확률 하한 → 귀납가정으로 얻는 closeness → 사건 포함에 따른 확률 단조성 → interleaved gap을 연결한다. |
| 주 정리 | `0`, `1`, `n+2`의 귀납 구조만 남기고 위 보조정리를 호출한다. JSONL의 명제 선언은 그대로 유지한다. |

사용되지 않는 cardinality 하한과 그 분모 소거·cast 코드를 제거했다. `ϑ_pred`, `hϑ`, `h_ϑ_pred` 등의 별칭·등식도 없앴다. 확률 부등식 연결은 `lt_of_lt_of_le`와 `Pr_le_Pr_of_implies`를 사용한다. 단순히 복잡한 코드를 다른 곳에 옮긴 것이 아니라 필요 없는 단계를 삭제하고, 샘플링 변환을 재사용 가능한 경계로 묶었다.

### 실제로 막힌 지점과 해결 과정

| 시도 | 관찰한 결과 | 해결·다음 시도 |
| --- | --- | --- |
| [1차](refactoring-07-12/P12/attempt_01.log): 보조정리 분리 및 `Fin.snoc_init_self`로 정규화 | `simp made no progress`와 `ModuleCode`→`Set` 인자의 타입 추론 오류 | 보조정리에 `A`, `ι`를 명시하고, `snoc` 재구성을 거치지 않는 샘플링 분할 형태로 변경했다. |
| [2차](refactoring-07-12/P12/attempt_02.log): 샘플링 등식을 `simpa only`로 한꺼번에 정규화 | 확률식 내부의 `Fin.init r`와 `fun i => r i.castSucc`가 맞지 않았다. 기저 단계의 일반적인 singleton 정리 적용도 진행되지 않았다. | 기저 단계의 사건 predicate를 명시했다. |
| [3차](refactoring-07-12/P12/attempt_03.log): `Fin.init`를 simp 목록에 추가 | 기저 단계는 해결됐지만 확률식 내부의 표현 불일치는 남았다. | 전체 확률식을 직접 단순화하는 방식에서 벗어났다. |
| [4차](refactoring-07-12/P12/attempt_04.log): 확률 함수에 `apply congrArg` 적용 | 고차 함수 인자의 단일화가 실패했다. | 각 샘플 `r`에서 사건 자체의 동등성을 먼저 증명하도록 바꿨다. |
| [5차](refactoring-07-12/P12/attempt_05.log): 점별 `fold` 등식과 `simp_rw` 사용 | 재귀식 rewrite 뒤 `Fin.init`와 lambda 사이의 정의적 동등성 목표가 남았다. | 그 작은 목표를 `rfl`로 닫았다. |
| [6차](refactoring-07-12/P12/attempt_06.log): 논리적 증명 완성 | 공리 목록에 `sorryAx`는 없었으나, sampling helper의 불필요한 `[Nonempty ι]`, `[DecidableEq ι]` 가정이 경고를 발생시켜 엄격 검증에 실패했다. | 해당 helper에만 `omit ... in`을 지정했다. 경고 검사를 끄지 않았다. |
| 최종 재실행 | 참조본·수정본 모두 종료 코드 0, 경고 오류 없음, 대상 정리의 `sorryAx` 없음 | [최종 수정본 로그](refactoring-07-12/P12/refactored.log)와 [결과 JSON](refactoring-07-12/P12/result.json)에 기록했다. |

실패 로그의 줄 번호는 각 시도 당시 파일 기준이다. 컴파일 오류가 있던 시도의 공리 출력은 성공 판정에 사용하지 않았다.

주 정리는 **177줄 → 17줄**이다. 새 보조정리·설명·`omit`·빈 줄을 합친 블록이 59줄이므로, 수정한 부분 전체는 **76줄**이다. 원본과 공유하는 앞부분 1,199줄의 문맥과 파일 끝의 검사 명령은 이 비교에서 제외했다.

### 남아 있는 범위와 한계

최종 대상 증명의 미해결 오류는 없다. 다만 기존 보조정리 문맥 1,199줄은 여전히 복원해서 사용한다. 이를 라이브러리 모듈로 재편하는 작업까지 수행한 것은 아니다.

ArkLib 의존성 빌드에서는 `ArkLib/Data/Fin/Basic.lean:307`과 `ArkLib/Data/MvPolynomial/Interpolation.lean:258`의 기존 `sorry` 경고가 재출력된다. 해당 라이브러리 전체가 `sorry` 없이 완성됐다는 뜻은 아니다. 이번 대상 정리의 실제 전이적 공리 목록에는 원본·수정본 모두 `sorryAx`가 없으며, 기존 라이브러리의 미완성 부분을 수정하지는 않았다.

## 로컬 실행 스크립트의 동작

기존 로컬 작업 폴더의 두 실행 스크립트는 참조본만 JSONL에서 재생성하고 수정본을 보존한다. 검증할 파일이 원래 명제 선언을 유지하는지 검사하고, 각 변형의 종료 코드·`sorryAx` 여부·경과 시간을 `result.json`에 저장한다. `reference.log`와 `refactored.log`는 가장 최근에 선택해 실행한 변형의 Lean 출력을 저장한다. `result.json`은 가장 최근 실행에서 선택한 변형들만 담으므로, 두 증명의 결과를 함께 갱신하려면 기본 명령 또는 `--variant both`를 사용한다.
