---
name: lean-refactor
description: "Refactor existing Lean 4 proofs while preserving theorem statements, verify the changes in the project environment, and compare proof size, elaboration cost, or version compatibility. Use for Lean proof cleanup, optimization, and Refactor Arena work, including repair of failures introduced by a refactoring. Not for general mathematics explanations or unrelated Lean feature development."
---

# Lean Refactor

기존 Lean 증명의 명제를 유지하면서 구조를 개선한다. 코드가 짧아졌다는 관찰과 Lean 처리 비용·버전 호환성의 개선을 구분한다. 사용자의 목표가 가독성, 길이, 비용 중 무엇인지 작업 맥락에서 판단하고 그 범위에 맞게 진행한다.

## 환경과 기준점

- 대상 저장소의 지침, `lean-toolchain`, Lake 설정, import, namespace, 로컬 보조정리와 변경 사항을 확인한다. 저장소의 고정된 환경에서 작업하며 모델이 기억하는 최신 Mathlib 환경으로 바꾸지 않는다.
- 정리의 명제와 원본 proof body를 구분해 보존한다. binder, 가정, 타입, attributes, surrounding definitions를 바꿔 목표를 쉽게 만드는 것은 증명 리팩터링이 아니다. 사용자가 명제 수정까지 요청했다면 별도 변경으로 설명한다.
- HEAD와 실제 작업 파일의 차이를 기록한다. 기존 사용자 수정은 기준점의 일부일 수 있으므로 복원하거나 덮어쓰지 않는다.
- 대상의 최소 빌드 명령으로 기준점이 검증되는지 확인한다. 원본 실패가 환경 문제인지 증명 문제인지 분리한다. 컴파일 가능한 기준점을 확보하지 못했다면 검증된 개선율을 주장하지 않는다.
- Arena 제출·평가 작업이면 [references/arena-and-strata.md](references/arena-and-strata.md)를 읽는다. 현재 규칙과 지정 revision은 대회 제공 자료에서 다시 확인한다.

## 구조를 이해한 뒤 수정

정리와 직접 관련된 정의·사용처를 읽고 “어떤 가정에서 무엇이 유지되는가?”를 한 문장으로 설명한다. 필요한 경우 작은 예제로 변수 수집, 치환, subset 등의 의미를 확인한다.

큰 연구 형식화의 검토를 요청받았거나 표현 간 변환이 핵심인 리팩터링이면 [references/research-formalization.md](references/research-formalization.md)를 읽는다. 최종 정리의 양화사 순서·비공허성, 정의의 실제 데이터, 표현을 잇는 bridge lemma, 조건부 보조정리의 가정 해소를 따라간다. 단순한 tactic 정리를 위해 저장소 전체 감사를 추가하지 않는다.

다음은 선택할 수 있는 전략이며, 고정된 tactic 순서가 아니다.

- 반복되는 경우 분석과 동일한 추론을 공통 절차나 기존 보조정리로 묶는다.
- 귀납적 불변식이 가정에 있다면 raw data에 대한 귀납과 그 증거에 대한 귀납을 비교한다. 증거 귀납이 항상 유리하다고 가정하지 않는다.
- 불필요한 `have`, 변수 재명명, 변하지 않는 대상의 단순화, 중복된 transitivity 연결을 줄인다.
- 로컬 정의에 맞게 unfold·split·simp 범위를 좁힌다. 광범위한 `simp_all`, 탐색 tactic, `repeat'`를 썼다면 비용과 실패 양상으로 적합성을 확인한다.
- 새로운 정리를 추측해서 넣기 전에 프로젝트의 선언과 검증된 예제를 검색한다. 비슷한 증명은 참고 자료이며 현재 목표에서 재검증해야 한다.

작은 후보부터 실제 Lean으로 확인한다. 오류가 나면 첫 진단, 남은 goal, 로컬 가설, 적용한 전략을 이용해 수정한다. 같은 실패를 반복하면 전략을 바꾸거나 마지막 검증된 후보로 돌아간다. 예산이 주어졌다면 실패·폐기한 모델 호출도 그 예산에 포함한다. 일상적인 코드 정리를 위해 별도 모델 호출 실험을 만들 필요는 없다.

## 검증과 측정

- 정리와 문맥이 유지되는지 diff로 확인하고, 최종 후보의 대상 모듈 및 직접 관련된 사용처를 검증한다. 전체 빌드는 변경 범위나 저장소 요구에 맞춰 선택한다.
- 큰 개발에서는 최종 정리의 줄 수와 전체 증명 의존성의 크기를 구분한다. 보조정리로 코드가 옮겨진 경우 측정 범위를 함께 밝힌다. import 그래프는 proof term의 실제 의존성 목록을 대신하지 않는다.
- 완성 증명에 새 `sorry`, 공리, unsafe 우회 또는 문제 정의 변경을 넣지 않는다. 원본과 후보의 `#print axioms`를 비교한다. 기본 목표는 공리 의존성도 유지하는 것이며, 사용자나 실제 평가 규칙이 다른 기준을 정하면 그 기준과 차이를 명시한다.
- 다른 선언의 기존 `sorry` 경고와 대상 정리의 `sorryAx` 의존성을 구분한다. 빌드 성공만으로 모든 정리가 완성됐다고 말하지 않는다.
- 참조 명제/Comparator challenge의 의도적인 `sorry` 자리와 구현 모듈의 미완성 증명을 구분한다. 검증 설정의 `permitted_axioms`는 허용 목록이며 실제 출력된 공리 목록이 아니다. 독립 검사 설정과 실행 결과도 구분한다.
- 길이는 proof body의 동일한 범위와 동일한 도구로 비교한다. 비어 있지 않은 줄·공백 제외 문자·Lean source token·모델 token은 서로 다른 지표다. 공식 tokenizer가 없으면 줄·문자 수를 보조 지표로 보고하고 공식 token 개선율은 미측정으로 남긴다.
- 비용은 지정된 harness 또는 프로젝트 측정 도구로 비교한다. cached/replayed build의 wall time을 proof elaboration 비용으로 사용하지 않는다. heartbeat, fresh elaboration 시간, 모델 API 비용을 별도 항목으로 기록한다.
- 호환성은 지정된 toolchain과 대응 repository revision에서 **같은 후보 코드**를 검증한 결과로 보고한다. 확인하지 않은 버전은 미측정이다.
- 가독성만 요청된 작업에 benchmark 실행을 자동으로 추가하지 않는다. 최적화·Arena 작업에서는 측정된 목표를 비교해 검증된 후보를 선택한다. 가장 짧은 후보가 비용·호환성에서도 가장 좋은 후보는 아닐 수 있다.

## 결과와 다음 개선

결과는 변경 이유, 검증 근거, 측정값 또는 미측정 항목, 남은 제한을 포함해 설명한다. 초보자용 자료라면 문제 뜻 → 작은 예제 → 원본 구조 → 수정의 이유 순서로 풀어 쓴다. 어려운 tactic 이름만 나열하지 않는다.

실험 기록은 프로젝트에 둔다. 필요한 항목은 problem/declaration ID, revision·toolchain, 기준 증명, 후보·전략, 검증 진단, 공리 목록, 측정 도구와 결과, 예산이 있는 경우 모델·호출 비용이다. 스킬 본문에 매 실행의 결과를 누적하지 않는다.

사용자가 스킬 개선을 요청하면 실제 사용에서 드러난 반복 가능한 교훈만 반영한다. 특정 예제의 tactic 파이프라인을 보편 규칙으로 승격하지 않는다. 프로젝트별 명령과 사례는 reference에 두고, 재사용할 작업 원칙은 이 파일에 둔다. 원본 스킬과 설치 복사본이 따로 있다면 요청된 수정 후 둘을 동기화한다.
