# Refactor Arena 공부 지도 — 문제를 이해하고, 증명을 개선하기

작성일: 2026-10-06 · 남성우의 warm-up 1·2 및 Autoformalization 조사용

## 1. 먼저 잡을 목표

Refactor Arena에서는 이미 정답인 Lean 증명을 받아 **같은 명제를 증명하는 더 나은 코드**를 만든다. 숙제 답을 바꾸는 일이 아니라, 정답에 이르는 설명을 정리하는 일이다. 목표는 증명 소스의 크기, Lean이 증명을 처리하는 비용, 다른 Lean 버전에서의 호환성이다. Track 1은 closed-source 모델 API를 사용하는 harness를 만들며 문제당 API 예산은 US$3 이하이다. [공식 워크숍 안내](https://vericodegen.github.io/#challenge-competition-track)

따라서 지금의 좋은 연구 질문은 다음이다.

> “명제와 공리 의존성을 유지하면서, 구조를 이해한 리팩터링이 단순 압축보다 길이·검증 비용·호환성을 잘 개선하는가?”

이 질문은 내가 제안하는 실험 방향이다. 논문의 결과나 아직 얻은 실험 결론은 아니다.

## 2. 세 가지 작업을 구분하자

| 작업 | 받는 것 | 만드는 것 | 핵심 질문 |
| --- | --- | --- | --- |
| Autoformalization | 사람 말로 된 문제·증명 | Lean 명제·증명 | 원래 뜻을 옮겼나? |
| Automated theorem proving | Lean 명제 | 그 명제의 Lean 증명 | 증명을 찾았나? |
| Proof refactoring | Lean 명제와 기존 증명 | 개선한 증명 | 같은 정답을 더 잘 설명하나? |

이번 warm-up은 세 번째다. Autoformalization 논문에서 배울 부분은 자연어 번역 모델 자체보다 **오류 피드백, 비슷한 예제 검색, 여러 목적의 평가, 의미 보존**이다.

```text
사람의 문제 ──형식화──> Lean 명제 ──증명 탐색──> 정답 증명
                           │                     │
                           └──── 명제 유지 ──────┤
                                                 ↓
                                            리팩터링 후보
                                                 ↓
                                    검증 → 측정 → 후보 선택
```

## 3. 지금 읽으면 흥미로울 논문

선정 기준은 LeanAgent README의 “피드백으로 수정, 제한된 예산, 재현 가능한 비교”와 현재 1·2번 문제다. 개인 취향을 알고 있다고 가정하지 않고, **Arena에 연결하기 쉬운 정도**로 추천한다.

| 우선순위 | 논문 | 흥미로운 질문 | Arena에 가져올 아이디어 |
| --- | --- | --- | --- |
| 1 | Process-Driven Autoformalization | 최종 실패 한 비트보다 첫 오류 위치가 더 유용할까? | 실패 위치와 goal을 기록하고 부분 수정하기 |
| 2 | ProofBridge | 사람의 증명 설명으로 비슷한 Lean 예제를 찾을 수 있을까? | “정규화 증거에 귀납” 같은 전략을 검색하기 |
| 3 | miniF2F-Lean Revisited | 벤치마크 정답이 원래 문제와 다르면 성공률은 무엇을 뜻할까? | 평가 단계와 실패 원인을 구분하기 |
| 4 | Herald | Lean 라이브러리에서 사람 말 학습 자료를 만들 수 있을까? | 로컬 정리의 설명과 검색 문맥 만들기 |
| 5 | NL2Lean | 컴파일 성공만 보상하면 충분할까? | 길이 외 비용·호환성을 함께 평가하기 |
| 6 | An Evaluation Benchmark for Autoformalization in Lean4 | 초기 번역 평가에서 무엇을 재고 무엇을 놓쳤을까? | 평가 방법을 읽는 연습 |

### Process-Driven: 가장 먼저 읽기

Lean 컴파일러의 피드백으로 과정 감독형 verifier인 PSV를 학습한다. 최종 결과만 평가하는 OSV와 달리 첫 오류 위치를 이용한 단계별 학습을 다룬다. **단순한 “컴파일 오류를 다시 프롬프트에 넣기” 시스템과는 구분해서 읽어야 한다.** [논문 v2, 방법 및 실험](https://arxiv.org/html/2406.01940v2)

ELI5: 선생님이 “틀렸어”만 말하는 대신 “여기까지는 맞고, 이 줄부터 틀렸어”라고 알려주는 셈이다.

읽을 질문: PSV의 정답 라벨은 어떻게 만들까? 컴파일 성공과 뜻이 맞는 번역을 어떻게 구분할까? 학습 없이 Track 1의 추론 루프에 빌려올 부분은 무엇일까?

**제안 실험:** 같은 모델·총예산에서 최종 성공/실패만 주는 수정과 첫 오류·goal·주변 정의를 주는 수정을 비교한다. 성공률, 수정 횟수, API 비용을 함께 남긴다. 이것은 논문 전체 재현이 아니라 아이디어를 옮긴 실험이다.

### ProofBridge: 시스템 설계가 재미있는 두 번째 선택

자연어와 Lean의 정리·증명 쌍을 공동 임베딩 공간에 놓아 예제를 검색하고, 정리와 증명 전체 번역 및 반복 repair에 이용한다. type correctness와 참조 Lean 명제에 대한 쌍방향 함의 기반 semantic correctness를 구분한다. [논문 v3](https://arxiv.org/html/2510.15681v3)

ELI5: 문제를 보고 풀이가 비슷한 예제 노트를 찾아 옆에 두고, Lean에게 검사받으며 고친다.

주의할 점: 참조 Lean 명제의 충실성을 가정한 동치 검사는 자연어 의미를 완전히 자동으로 검증했다는 뜻이 아니다. 또한 참인 두 닫힌 명제 사이의 논리적 동치만으로 문제 표현의 구조적 충실성을 모두 보장할 수 없다. 후자는 평가 방법에 대한 우리의 해석이다.

**제안 실험:** 검색 없이 수정하기와, 로컬 AST/subset 증명 및 전략 설명을 검색해 수정하기를 비교한다. “자연어→Lean 번역”을 “기존 증명→개선 전략 검색”으로 바꾸는 응용이다. 현재 문제나 정답을 검색 데이터에 섞지 않는다.

### miniF2F-Lean Revisited: 평가 감각을 키우는 선택

자연어 문제 이해→형식화→증명을 모두 평가하고, miniF2F의 자연어와 formal statement 불일치를 분석한다. 개별 단계의 높은 성능이 전체 파이프라인 성공을 의미하지 않는다는 점이 핵심이다. [논문](https://arxiv.org/html/2511.03108v1)

ELI5: 숙제를 잘 풀어도 애초에 다른 숙제를 풀었다면 원래 숙제의 정답은 아니다.

Arena에서는 주어진 명제를 고정하므로 매번 번역 동치를 증명하기보다, **명제·환경의 무변경 확인**이 먼저다. 성공률에도 “컴파일 통과”, “공리 확인”, “공식 평가 통과”라는 서로 다른 층이 있다.

### Herald: 데이터와 설명을 만드는 방향

Mathlib4의 Lean 자료를 자연어로 옮겨 대응 데이터를 만들고, 증강과 이를 이용한 translator 학습을 다룬다. 출발 방향이 Lean→자연어라는 점이 재미있다. [논문 v2](https://arxiv.org/abs/2410.10878v2)

ELI5: 이미 채점된 정답 코드 옆에 사람말 설명을 붙여 문제집을 만든다.

**제안 응용:** warm-up에 필요한 정의·보조정리마다 “무슨 뜻인가 / 언제 쓰나 / 예제 / 검증된 버전”을 붙인다. Mathlib 기반 데이터의 성과가 Strata에도 그대로 적용된다고 가정하지 않는다. 초록의 pass@128도 한 번 시도의 성공률과 구분한다.

### NL2Lean: 학습과 보상 설계에 관심이 생겼을 때

ReLean은 자연어→Lean statement 번역에 semantic, term-level, global-level, compile-checking의 네 보상 축과 PPO 및 curriculum learning을 이용한다. [ACL 공식 논문 안내](https://aclanthology.org/2025.emnlp-main.1586/)

ELI5: 받아쓰기를 채점할 때 문법뿐 아니라 뜻과 구조도 본다.

당장 Track 1에서 모델을 학습할 필요는 없다. “짧으면 무조건 좋다”는 후보 선택 규칙을 버리고, 컴파일 통과를 먼저 확인한 뒤 길이·heartbeat·호환성을 비교하는 사고방식을 빌려오자. 이 세 지표는 Arena에 맞춘 응용이며 NL2Lean의 원래 보상과 동일하지 않다.

### 초기 평가 논문: 짧은 배경 읽기

An Evaluation Benchmark for Autoformalization in Lean4는 GPT-3.5, GPT-4, Gemini Pro 등을 대상으로 Lean4 형식화 능력을 평가한 초기 연구다. 현재 모델 순위를 판단하기보다 평가 과제와 채점 기준을 보는 자료로 적합하다. [논문](https://arxiv.org/abs/2406.06555)

읽을 질문: 입력은 명제인가 증명까지인가? 성공을 컴파일로 정하는가 사람이 뜻도 확인하는가? 재시도 예산과 난도는 통제했는가?

### Arena 목표에 가장 직접적인 추가 논문

목록 34번 **Lean Refactor**도 함께 읽자. 버전·컴파일 비용 정보를 붙인 전략 은행을 검색하여 frozen LLM의 반복 리팩터링을 유도하는 연구다. 길이·컴파일 비용·호환성이 충돌할 수 있다는 문제 설정이 지금 작업과 직접 연결된다. [논문 v2](https://arxiv.org/html/2605.20244v2)

권장 순서: warm-up ELI5 → Lean Refactor의 문제 설정·방법 → Process-Driven → ProofBridge → miniF2F Revisited. Herald와 NL2Lean은 설명 데이터나 학습으로 관심이 확장될 때 읽자.

## 4. 1·2번에서 출발하는 작은 연구

문제 설명은 [warm-up ELI5 노트](../../meetings/2026-10-11-week2/warmup-problems-1-2-eli5.md), 그림과 코드 비교는 [HTML 보고서](../../meetings/2026-10-11-week2/warmup-problems-1-2.html)를 보자.

| 비교 | 바꾸는 요소 | 확인하고 싶은 것 |
| --- | --- | --- |
| baseline vs 구조 설명 제공 | AST·old·subset 설명 | 이해가 후보 품질을 개선하는가? |
| 최종 실패 vs 상세 피드백 | 첫 오류와 goal | 같은 예산에서 repair가 효율적인가? |
| 검색 없음 vs 전략 검색 | 비슷한 증명/전략 | 불필요한 시도를 줄이는가? |
| `induction post` vs `induction h` | 귀납 대상 | 2번의 구조 개선이 비용에도 유리한가? |

한 번에 한 요소를 바꾸고 모델·프롬프트 기본 틀·총예산을 맞춘다. 2문제의 결과는 사례 분석으로 보고 일반 성능 결론은 별도 문제 세트에서 검증한다. warm-up에서 전략을 개발했다면 그 성과는 개발 세트 성과라고 표시한다.

최소 로그 항목:

```text
problem_id, repository_commit, lean_version, candidate_id, parent_candidate_id
strategy, model/provider/version, prompt, response, input/output_tokens, api_cost
compile_result, first_error, remaining_goals, axiom_dependencies
proof_source_tokens, heartbeats, version_results, wall_time
```

실패·폐기한 호출도 비용에 포함해 기록한다. API 비용과 Lean의 heartbeat는 서로 다른 예산이다. 가장 짧은 후보 하나만 저장하지 말고, 길이와 비용 중 어느 쪽도 일방적으로 더 나쁘지 않은 후보들을 남긴다.

## 5. 공부 순서와 완료 기준

1. **문제 이해, 30분:** ELI5 노트의 예제를 손으로 계산하고 1번의 `[h1]`, 2번의 정규화 가정을 설명한다.
2. **Lean 읽기, 45분:** `OldExpressions.lean`의 세 정의와 `getVars`를 읽고 코드와 예제를 연결한다.
3. **리팩터링 이해, 45분:** 원본에서 반복되는 분기를 표시하고 `induction h`를 말로 설명한다.
4. **논문, 각 45분:** 방법 그림과 평가 기준부터 읽고, 가져올 아이디어·맞지 않는 가정·실험 한 개를 적는다.
5. **평가 준비:** heartbeat와 공식 tokenizer의 측정 방법을 확보하고, 원본과 후보를 같은 환경에서 비교한다.

발표는 “문제 뜻 2분 → 핵심 리팩터링 2분 → 확인한 결과와 남은 측정 1분 → 논문 기반 실험 2분”이면 충분하다.

현재 확인한 범위는 Lean v4.26.0의 모듈 빌드와 두 정리의 원본/후보 공리 목록이다. 공식 평가 점수, heartbeat 개선, 다른 버전 호환성, 대회 실행 비용은 아직 확인하지 않았다.

## 6. 로컬 자료와 재현

워크스페이스 루트 기준:

- `LeanAgent/README.md`: 프로젝트 목표와 로드맵.
- `refactor_arena/benchmark_data_warmup.jsonl`: 원본 명제·증명·버전 정보.
- `refactor_arena/strata/Strata/Languages/Core/OldExpressions.lean`: old 치환·추출·정규화 정의.
- `refactor_arena/strata/Strata/DL/Lambda/LExpr.lean`: 변수 목록 정의.
- `refactor_arena/strata/Strata/Transform/CallElimCorrect.lean`: 리팩터링된 두 정리와 사용처.
- `refactor_arena/verify_warmup_1_2.lean`: 원본 재검증과 원본/후보 `#print axioms`.

```sh
cd /Users/sungwoo/lean_project/refactor_arena/strata
lake build Strata.Transform.CallElimCorrect
lake env lean ../verify_warmup_1_2.lean
```

Strata HEAD는 `451e5f047bafa010d178856db76c00029bfa4d7f`, toolchain은 `leanprover/lean4:v4.26.0`이며 두 증명의 로컬 수정이 적용된 상태다. 이를 순정 HEAD 결과로 표현하지 않는다.
