# 검증/수리 설계 참고자료·메모 (W03-2)

Arena의 검증 기준과 오류 피드백을 이용한 수리 절차를 검토하기 위한 후속 메모입니다. 시스템별 상호작용 비교, APOLLO 분석, 간단 예제의 실행 관찰과 최소 실행 구조 제안을 정리합니다.

- 작성: 손지연 · 검증/수리 설계
- 날짜: 2026-10-18 (Markdown 정리)
- 상태: 참고자료·실행 관찰 메모·설계 제안. 비교 실험과 모듈 설계는 제안 단계이며 구현·검증 결과가 아닙니다.
- 관련 문서: [분야 자료 안내](../../README.md) · [대표 보고서](report.html) · [상위 프로젝트](https://app.notion.com/p/Lean-Agent-3e94325d9a27800ebb84e557ee5bad6a?pvs=21)

## 1. 이번 주 조사 과제

| 전체 과제 | 검증·수리 담당이 답할 질문 | 가져갈 산출물 |
| --- | --- | --- |
| 기존 Lean agent·proof repair·harness 조사 | 어떤 정보를 Lean에 보내고, 실패하면 무엇을 받으며, 그 정보로 무엇을 수정하는가? | 시스템별 입출력·수정 단위·종료 조건 비교표 |
| 공개 시스템 실행 및 상호작용 비교 | 실제 오류 메시지와 proof state가 다음 수정에 어떻게 연결되는가? | 정상 → 오류 → 수정 → 재검증의 코드와 로그 |
| 프로젝트 최소 실행 구조 설계 | 검증기·모델·controller가 각각 무엇을 책임지고, 언제 성공·중단을 선언하는가? | 모듈 구조, 데이터 형식, 성공 기준, 재시도 정책 |

## 2. 설계 범위

- 검증: Lean 커널의 검사와 함께 원래 명제를 바꾸지 않았는지, `sorry`나 허용되지 않은 공리에 의존하지 않는지 확인합니다.
  - 실행의 종료와 요구한 증명의 완성을 구분합니다.
- 수리:
  - 오류 메시지만 모델에 전달할지, 남은 목표와 가정까지 전달할지 검토합니다.
  - 실패한 부분만 수정할지, 증명 본문 전체를 재작성하게 할지 검토합니다.

## 3. 단계 초안

| 단계 | 처리 내용 |
| --- | --- |
| 검증 | Lean 커널 검사 결과와 원래 명제·환경 유지 여부, 허용 공리 기준 확인 |
| 진단 | 오류 메시지 확인<br>예: 제출한 항의 타입 ≠ 필요한 타입 |
| 정보 전달 | 현재 목표와 가정<br>실패한 코드와 실제 오류 메시지 |
| 수정 | 실제 코드 → 수정 코드 |
| 재검증 | 수정한 증명이 원래 명제를 해결하는지 전체 파일을 다시 실행하고 성공 기준 확인 |

## 4. 기준·수정 범위 초안

### 4.1. 성공·피드백·종료 기준

| 질문 | 제안 기준 |
| --- | --- |
| 무엇을 성공으로 인정하는가? | 원래 명제·환경 유지<br>Lean 검사 및 허용 공리 검사 통과 |
| 어떤 피드백을 전달하는가? | 실패한 코드<br>실제 오류 메시지<br>오류 위치<br>확보 가능한 현재 목표와 가정 |
| 어디까지 수정하는가? | 명제·가정·주변 정의·의존성은 고정 |
| 언제 재시도·중단하는가? | 최대 3회 수정<br>별도 종료 사유 기록: 같은 후보 반복, 실행 시간 초과, 예산 소진 |
| 무엇을 기록하는가? | 입력 코드, 피드백, 수정 코드, 실행 명령·버전, 결과, 시도 횟수, 시간, 모델 사용량 |

허용 공리 목록과 시간·토큰 예산의 구체적인 값은 후속 설계에서 정해야 합니다.

### 4.2. 증명 본문과 전체 Lean 파일의 역할

모델이 참고하는 문맥, 모델이 수정하는 범위, Lean이 최종 검증하는 대상을 구분합니다. 아래는 비교 실험을 준비하기 위한 수정 범위 제안입니다.

| 구분 | 제안 방식 |
| --- | --- |
| 모델이 참고하는 정보 | 정리문 + 필요한 문맥 + 증명 본문(proof body) + Lean 오류 |
| 모델이 출력하는 수정 결과 | 수정된 증명 본문 |
| Lean이 최종 검증하는 대상 | 수정된 증명을 반영한 전체 Lean 파일 |

| 상황 | 적합한 수정 범위 |
| --- | --- |
| `exact`에 잘못된 증거 전달 | 증명 본문 |
| `rw`, `simp` 적용 실패 | 증명 본문 |
| 증명 안에 보조 사실 `have` 추가 | 증명 본문 |
| 별도의 보조정리 선언 필요 | 여러 선언에 걸친 수정 |
| 정의·명세 자체에 결함 존재 | 명세 수정 검토를 위한 별도 절차 |

여러 선언이나 명세의 수정이 필요한 경우에는 위의 증명 본문 수리 범위와 구분해 검토합니다.

### 4.3. 실패 종류 후보

- 증명 오류
- 환경·의존성 문제
- 시간·예산 초과

## 5. 참고자료·시스템 비교

### 5.1. 우선 읽을 자료

| 자료 | 링크 | 읽을 부분 | 가져올 설계 아이디어 |
| --- | --- | --- | --- |
| **Lean 공식 문서 — Validating a Lean Proof** | [Lean Reference Manual](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) | 성공 확인, 공리 의존성 검사 부분 | 어떤 결과를 믿을 수 있는가? |
| **APOLLO** | [arXiv 2505.05758](https://arxiv.org/abs/2505.05758) · [본문 (v5)](https://arxiv.org/html/2505.05758v5) · [분석 메모 기준 본문 (v3)](https://arxiv.org/html/2505.05758v3) | §3 *Our Approach*, Appendix B의 수리 사례 | 실패한 증명의 일부를 어떻게 분리하고 다시 고치는가? |
| **Pantograph / PyPantograph 문서** | [GitHub](https://github.com/stanford-centaur/PyPantograph) · [Introduction](https://github.com/stanford-centaur/PyPantograph/blob/main/doc/intro.md) · [Goals and Tactics](https://github.com/stanford-centaur/PyPantograph/blob/main/doc/goal.ipynb) | *Introduction*, *Goals and Tactics* | 프로그램이 Lean의 목표와 실행 결과를 어떻게 다루는가? |

### 5.2. 모델과 Lean의 상호작용

| 대상 | 모델과 Lean의 상호작용 | 검증·수리 관점에서 가져올 점 | 링크 |
| --- | --- | --- | --- |
| **LeanAgent 논문 시스템 / LeanDojo 계열** | 현재 proof state에서 tactic 후보를 생성하고, Lean으로 실행하여 다음 상태를 얻습니다. LeanAgent는 이를 탐색 트리로 관리하고 막히면 다른 경로를 시도합니다. | 후보 생성과 후보 실행을 분리하고, 실패한 후보와 마지막 유효 상태를 구분합니다. | [LeanAgent 논문 (v8)](https://arxiv.org/html/2410.06209v8) |
| **community REPL / LeanInteract** | 전체 코드·파일을 검사하거나, 특정 proof state에 tactic을 실행합니다. 오류, 위치, `sorry`, 환경·상태 식별자 등을 받을 수 있습니다. | 프로젝트의 검증 adapter를 만드는 기반입니다. LeanInteract는 이 상호작용을 Python에서 다루기 위한 인터페이스입니다. | [community REPL](https://github.com/leanprover-community/repl) |
| **APOLLO** | Lean의 진단으로 실패한 부분을 찾아 구문을 수정하고, 자동 tactic을 적용하며, 남은 부분을 LLM으로 수리해 다시 조립합니다. | 실패 위치와 지역 문맥(local context)을 보존하고, 필요한 부분에 수정 시도를 집중하는 방법을 참고합니다. | [APOLLO 본문 (v5)](https://arxiv.org/html/2505.05758v5) |
| **APRIL — Learning to Repair Lean Proofs from Compiler Feedback** | 잘못된 증명과 compiler feedback을 입력으로 받아 수정 증명과 진단 설명을 학습·평가합니다. | 오류 사례를 어떤 데이터로 저장할지 참고합니다. 핵심 평가는 단발 수리이며 반복 harness 자체는 아닙니다. | [arXiv 2602.02990](https://arxiv.org/abs/2602.02990) |
| **mini-Lean-agent** | 모델은 bash로 파일을 읽고 수정하며 Lean을 실행합니다. 제출 후에는 별도의 평가기가 최종 결과를 검증합니다. | 에이전트가 작업을 끝낸 것과 증명이 검증된 것을 구분하는 구조를 참고합니다. 원문에서는 2026-10-12 제출 사례로 기록했습니다. | [GitHub](https://github.com/TomasOrtega/mini-lean-agent) |
| **Claude Agent SDK 같은 일반 harness** | 모델의 도구 호출 → 실행 → 결과 반환을 반복하고, 세션·사용량·실행 한도를 관리합니다. | 반복·예산·로그 기능을 참고하되, Lean 증명 성공 기준은 프로젝트에서 별도로 정의해야 합니다. | [Agent loop 문서](https://code.claude.com/docs/en/agent-sdk/agent-loop) |

## 6. 논문 조사 메모: APOLLO

> 전체를 버리고 다시 생성할 것인가, 기존 구조를 보존하고 실패한 부분만 고칠 것인가?

### 6.1. 개요와 피드백 구조

**APOLLO: Automated LLM and Lean Collaboration for Advanced Formal Reasoning**

(**A**utomated **P**r**O**of repair via **L**LM and **L**ean c**O**llaboration)

APOLLO는 LLM이 생성한 증명에서 구문 오류와 실패한 부분을 찾아 분리하고, 자동화 도구와 LLM을 이용해 남은 목표를 해결한 뒤 조립한 증명을 재검증하는 절차입니다. 남은 목표별 LLM 호출에는 작은 top-K 예산을 사용합니다. 기존 증명 구조를 활용한 부분 수리 설계를 조사하는 데 참고합니다.

- 기존 방식의 피드백: 성공·실패의 이진 판정.

- APOLLO의 피드백: 구문 오류, 잘못된 tactic, 남은 목표 등의 상세 정보.

### 6.2. 단계별 접근

구문 정리 → 실패 부분을 `sorry`로 분리 → 자동 풀이 → 남은 부분의 LLM 수리 → 증명 조립·재검증 순서로 진행합니다. 논문은 이 단계적 접근으로 증명 샘플 효율과 최종 증명 정확도를 개선한다고 설명합니다.

Lean REPL은 컴파일 오류와 경고의 설명·위치를 제공합니다. APOLLO는 구문 실수, 존재하지 않거나 사용되지 않는 tactic 등의 진단 정보를 모아 동적 코드 수리와 하위 문제 추출에 사용합니다.

전체 의사 코드는 논문 부록의 [Algorithm 1](https://arxiv.org/html/2505.05758v3#alg1)을 참고합니다.

### 6.3. Syntax Refiner: 구문 정리

- Lean 4 구문에 특화되지 않은 모델이 만든 구문 실수를 정규화합니다.
- 뒤따르는 단계가 문법적으로 유효한 코드를 입력받도록 합니다.

### 6.4. Sorrifier: 실패한 부분 분리

- 실패한 증명을 중첩된 증명 블록의 트리로 파싱하고 Lean REPL로 컴파일합니다.
- 남아 있는 컴파일 실패에 다음 수리를 적용합니다.
  - **줄 제거**: tactic 하나나 선언이 잘못되었지만 주변 블록은 성립할 수 있는 경우.
  - **블록 제거**: 하위 증명 전체의 구조가 잘못된 경우.
  - **`sorry` 삽입**: 블록의 타입 검사는 진행되지만 미해결 목표가 남은 경우.
- 컴파일 오류가 없어질 때까지 반복합니다.
- 남아 있는 `sorry`는 이후 단계에서 증명해야 할 하위 목표로 다룹니다.

여기서 `sorry`는 중간 수리 단계의 표시이며 최종 증명의 성공 기준과 구분합니다.

### 6.5. Auto Solver: 자동 풀이

- 각 `sorry` 블록을 대상으로 Lean 4의 `hint`를 사용해 목표 해결을 시도합니다.
- 목표가 남으면 `nlinarith`, `ring`, `simp` 등의 내장 solver를 `try`로 감싼 조합을 자동으로 시험합니다.
- `sorry` 없이 증명이 완성되면 해당 수리가 성공한 것으로 보고, 해결되지 않은 부분은 재귀 수리 단계로 넘깁니다.

### 6.6. Recursive Repair: 재귀 수리

- 남아 있는 실패 부분을 새로운 하위 보조정리로 간주합니다.
- 가정, 정의, 앞서 증명한 보조정리 등 지역 문맥을 추출하여 LLM에 전달합니다.
- 생성한 하위 증명에 검증, 구문 정리, Sorrifier, Auto Solver 과정을 다시 적용합니다.
- 사용자가 지정한 재귀 깊이 `r`까지 추가 수리와 하위 증명 생성을 진행합니다.

### 6.7. Proof Assembler: 조립과 재검증

- 복구된 블록을 하나의 파일로 모으고 `sorry`나 `admit`이 남지 않았는지 확인합니다.
- 조립한 증명을 다시 검증합니다.
- 여전히 실패하면 재귀 깊이 `r`의 범위 안에서 전체 파이프라인을 반복합니다.

## 7. 비교 실험 질문

> **같은 실패한 증명을 고칠 때, 오류 메시지만 주는 것보다 현재 목표와 가정까지 제공하는 것이 도움이 되는가?**

| 방식 | 모델에 제공하는 정보 |
| --- | --- |
| **A: 오류 메시지 기반 수리** | 원래 명제 + 실패한 증명 + Lean 오류 메시지 |
| **B: 목표·가정 포함 수리** | A의 정보 + 실패 지점에서 확보한 현재 목표와 가정 |

- 공통: 같은 실패 코드, 같은 모델, 같은 수정 범위.
- 관찰: 실제 수리 성공 여부, 수정 횟수, 어떤 정보가 사용됐는지.
- 사용량 기록: 입력 길이와 총토큰.

위 비교는 실험 설계 질문이며 A/B 비교 결과는 원문에 포함되어 있지 않습니다.

## 8. 상호작용 확인 질문·실행 관찰 메모

### 8.1. REPL의 요청·응답에서 확인할 것

검증·수리 담당은 도구의 사용 가능 여부와 함께 다음을 확인해야 합니다.

- 전체 증명을 보내는가, tactic 하나를 보내는가?
- 오류 위치를 받을 수 있는가?
- 실패 직전의 가정과 목표를 받을 수 있는가?
- 실패한 뒤 이전 상태에서 다시 시도할 수 있는가?
- 그 결과가 실제 파일에 반영되는가?

### 8.2. 최종 검증 책임과 도구 선택

원문에서 조사한 [mini-Lean-agent README](https://github.com/TomasOrtega/mini-lean-agent)는 모델이 파일을 수정·검사하고 제출하면 별도 검증 프로젝트의 Comparator가 원래 정리와 제출 증명을 검사한다고 설명합니다. 제출 후 추가 수리는 하지 않는 구조입니다. 최종 수락을 누가 책임지는지 명확히 하는 데 참고합니다.

이후 tactic 단위 분기 탐색까지 구현한다면 [PyPantograph](https://github.com/stanford-centaur/PyPantograph)도 비교합니다. 원문에서는 tactic 실행, metavariable 간 연결 처리, 전체 파일의 명세 일치(specification conformity) 검사를 비교할 기능으로 기록했습니다.

### 8.3. 간단 예제 실행 관찰

아래는 HTML 원문에 기록된 실행 관찰입니다. 실행 코드와 원시 로그는 원문에 첨부되어 있지 않습니다.

- 환경: Lean 4.19.0 + community REPL v4.19.0.
- 정상 → 오류 → 수정 흐름을 확인했다고 기록했습니다.
- `sorry`가 남은 파일도 있으므로 `exit code == 0`만으로 성공을 판정할 수 없습니다.
- `goals = []`만으로도 최종 증명 성공을 판정할 수 없습니다.

| 값 | 의미 |
| --- | --- |
| `goals = null` | 목표 정보를 얻지 못했거나 해당 응답에서 제공하지 않음 |
| `goals = []` | backend가 실제로 빈 목표 목록을 반환함 |
| `goals = [...]` | 남은 목표가 있음 |

tactic 실행을 끝냈다고 원래 파일이 수정되는 것은 아닙니다. 수정 후보를 완성한 뒤 실제 전체 코드에 반영하고 전체 정리를 재검증해야 합니다.

### 8.4. 설계에 반영할 점

- `verify`는 실제 전체 파일·해시·고정 환경·대상 정리를 입력받아야 합니다.
- 피드백에는 위치, 기대 타입과 실제 타입, 목표와 지역 문맥이 필요합니다.
- 증명 오류와 환경 실패·시간 초과를 구분하고, 수정 범위와 재시도 예산을 제한해야 합니다.
- 최종 성공은 전체 파일 재검증과 전이적 공리 비교로 결정해야 합니다.

## 9. 최소 실행 구조 제안

### 9.1. 검증·수리 흐름

[대표 보고서의 최소 검증·수리 흐름](report.html#minimal-design)을 참고합니다.

### 9.2. 구성 요소와 책임

| 구성 요소 | 최소 책임 |
| --- | --- |
| **TaskSpec** | 원본 정리, source commit, Lean 버전, 의존성, 수정 가능한 범위를 고정 |
| **LeanRunner / 검증 adapter** | Lean을 실행하고 실제 오류·위치·목표·상태를 반환 |
| **RepairPolicy / 모델 adapter** | 현재 증명과 실제 피드백을 받아 수정된 증명 본문 제안 |
| **Controller** | 후보 적용, 재검증, 시도 횟수·시간 제한, 중복 처리 |
| **FinalVerifier** | 실제 반영된 전체 파일과 원래 정리의 수락 기준 확인 |
| **Trace** | 후보, 변경 내용, 검증 명령, 원시 응답, 시간, 종료 사유 저장 |

### 9.3. 검증 결과 스키마 초안

다음은 응답 형식 예시이며 실제 실행 로그가 아닙니다. `null`은 해당 정보를 확보하지 못한 상태로 두고 빈 목록과 구분합니다.

```json
{
  "task_id": "warmup_07",
  "attempt": 1,
  "status": "proof_error",
  "process_exit_code": 0,
  "diagnostics": [
    {
      "severity": "error",
      "position": {"line": 3, "column": 4},
      "message": "실제 Lean 오류 원문"
    }
  ],
  "goals": null,
  "sorries": null,
  "statement_check": "not_run",
  "axioms": null,
  "raw_log_path": "attempt_01.raw.json"
}
```

### 9.4. 검증·실패 상태와 다음 행동

| 상태 | 의미 | 다음 행동 |
| --- | --- | --- |
| `candidate_pass` | 예비 검사 통과 | 전체 파일 최종 검증 |
| `proof_error` | 타입·구문·tactic 오류 | 오류를 모델에 전달해 수정 |
| `incomplete` | 남은 목표 또는 `sorry` 의존 | 수리 계속 |
| `invalid_candidate` | 수정 범위 이탈 또는 고정 문제 변경 | 후보 거절 |
| `timeout` | 시간 내 판정을 얻지 못함 | 자원 실패로 기록하고 별도 정책 적용 |
| `environment_error` | toolchain·설치·고정 의존성 문제 | 환경 점검 |
| `verified` | 최종 수락 기준 충족 | 성공 종료 |

## 10. 실행 기록 항목·명령 메모

```text
- model/version
- prompt
- response
- token/cost
- candidate proof
- Lean result/error
- proof length
- elaboration metric
- toolchain/repo commit
```

아래 명령은 실행·사용량 추출 예시이며 이 문서의 검증 기록이 아닙니다. `Typing.progress`와 출력 파일명은 실제 대상에 맞게 바꿔야 합니다.

```sh
codex exec --json \
  "Refactor only the Typing.progress proof and verify it." \
  > warmup_07.jsonl
```

이후 다음 명령으로 모델 사용량을 추출할 수 있습니다.

```sh
jq 'select(.type == "turn.completed") | .usage' warmup_07.jsonl
```
