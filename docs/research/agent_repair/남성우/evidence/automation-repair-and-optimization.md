# 자동화 수리 후 heartbeat 최적화

2026-10-13. 사용자 지적 반영: simp/aesop으로 correctness를 회복해도 최종 점수가 좋아진다는 뜻은 아니다. 아래는 설계 검토이며 Arena 대상의 실제 heartbeat 비교 실험 전이다.

## 검토 근거

- [Lean Refactor Appendix D](https://arxiv.org/html/2605.20244v1)는 interval_cases/simp_all/nlinarith가 많은 분기에 적용되는 짧은 증명과 긴 명시적 증명을 비교하고, 짧은 코드가 더 비쌀 수 있음을 보인다.
- [Lean 공식 simp? 설명](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)은 필요한 simp 규칙을 제안하는 기능을 설명한다.
- [Aesop proof scripts](https://github.com/leanprover-community/aesop)는 aesop?가 성공한 tactic script를 출력하며 proof trace도 제공함을 설명한다.

단순 tactic 이름만으로 비용을 예측할 수 없다. simp는 작은 목표를 저렴하게 해결할 수도 있고 넓은 가설·규칙 집합을 반복 처리할 수도 있다. aesop은 탐색 비용이 있지만 직접 증명과 비교한 실제 결과가 필요하다. 명시적 script도 크기·elaboration 비용·버전 호환성을 다시 측정해야 한다.

## 세 가지 proof 상태를 구분

| 상태 | 의미 | 처리 |
|---|---|---|
| invalid | 아직 미완성/검사 실패 | repair 요청 |
| valid | 원래 명제의 완성된 증명 | 점수 측정, 원본·best와 비교 |
| selected | combined가 개선되고 최종 검증됨 | 현재 최선으로 보관 |

자동화로 얻은 valid proof는 최종 결과이거나 추가 최적화의 출발점이다. 거기서 탐색을 무조건 중단하지 않는다.

## 수정한 파이프라인

```text
실패 후보
  → 로컬 자동화로 valid proof 확보
  → 탐색 결과를 명시적 proof로 추출
  → raw 자동화와 추출 proof를 모두 검증·측정
  → 원본/best와 combined 비교
  → 필요하고 API 예산이 있으면 LLM optimization 요청
  → LLM 후보 재검증·재측정
  → 평가한 유효 후보 중 최고점; 개선 없으면 원본
```

첫 로컬 최적화는 simp?→simp only, aesop?→명시적 script, exact?→exact lemma 같은 탐색 제거다. 추출된 proof에는 다른 자동화가 남을 수 있으므로 ‘검색 없는 proof’라고 자동 가정하지 않는다. 목표 환경에서 지원되는 기능만 사용한다.

예시 후보(동등한 작은 증명이며 수치 개선을 보장하지 않음):

```lean
example (x : Nat) : (x + 0) + 0 = x := by simp
example (x : Nat) : (x + 0) + 0 = x := by simp only [Nat.add_zero]

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by aesop
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by exact ⟨h.2, h.1⟩
```

## LLM에 무엇을 전달할까?

실패 repair와 성공 optimization 요청은 구분한다. optimization packet에는 명제·고정 문맥, 원본, 자동화로 해결한 proof, 추출 script, 핵심 적용 lemma, 가능하면 expensive tactic 위치, 전체 후보의 token/HB/버전 결과와 현재 best를 준다.

요청 예: ‘이미 검증된 proof다. 명제와 imports를 유지하고 넓은 자동화/반복 분기를 더 좁은 lemma 적용이나 명시적 추론으로 바꾸어 combined를 높이는 후보를 제안하라.’ 목표가 단순히 correctness가 아니므로 원본 대비 길이/HB/robustness trade-off를 함께 전달한다.

대상 theorem이 여전히 실패하면 기존 repair packet을 사용한다. profiling이 없으면 병목 위치를 추측으로 단정하지 않고 전체 수치와 자동화 사용 위치를 제공한다.

## 언제 호출할까?

API $3는 생성·repair·optimization이 공유한다. 아래 조건은 조사에 기반한 시작 정책이며 성공 확률을 측정한 기준이 아니다.

- valid 후보가 있지만 combined가 원본/best보다 낮거나 넓은 탐색이 주된 비용이면 optimization 대상으로 우선 고려.
- token은 줄었지만 heartbeat가 크게 증가한 후보는 명시적 추출을 먼저 시험하고, 그래도 좋지 않으면 모델 최적화 후보로 보관.
- 이미 개선된 후보도 budget이 남고 개선 여지가 있으면 추가 최적화 가능.
- rfl/exact처럼 작은 명시적 proof로 충분하면 불필요한 model round를 생략.
- raw 자동화가 현재 최고 combined라면 그대로 보관. 자동화라는 이유만으로 버리지 않음.

best valid는 LLM 호출 중에도 보존한다. LLM 후보가 실패하거나 악화되면 기존 best로 돌아가고, 어떤 후보도 원본보다 높지 않으면 원본을 반환한다. 모든 같은 body의 지정 버전 결과를 비교한다. 탐색 때 총 사용한 heartbeat와 최종 제출 proof의 heartbeat는 별개다.

## 검증 데이터와 비교 실험 추가

동일한 initial candidate와 API cap으로 다음 경로를 비교한다.

| 경로 | 구성 |
|---|---|
| A | Lean 진단 → 곧바로 LLM repair/optimization |
| B | 로컬 자동화 → raw proof 채점 |
| C | 로컬 자동화 → 명시적 script 추출 → 채점 |
| D | C → 선택적 LLM optimization → 채점 |

초기 후보와 무관한 정답 proof를 model에 노출하지 않는다. D의 추가 호출은 A와 같은 per-problem cap에서 비교하고, API 비용뿐 아니라 최종 combined와 fallback 비율을 보고한다.

데이터에는 ‘정확하지만 heartbeat 악화’, ‘HB는 개선하지만 token 증가’, ‘script 추출 후 버전 실패’, ‘LLM 최적화 실패 후 best 보존’, ‘raw 자동화가 최고점’, ‘모든 경로 원본 이하’를 포함한다. 가상 metric fixture와 실제 측정을 구분한다.

성능 결론은 이 비교 실험 뒤에 낸다. 현재는 ‘로컬 자동화 다음 모델 최적화’가 타당한 설계 후보라는 판단이다.
