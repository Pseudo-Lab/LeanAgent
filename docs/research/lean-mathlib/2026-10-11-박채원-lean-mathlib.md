# Lean&Mathlib: Mathematics in Lean 2장 Basics 풀이·개념 정리

- 분야: `Lean&Mathlib`
- 공유일: 2026-10-09 (초안) · 발표: 2026-10-11 W02
- 교재: Jeremy Avigad, Patrick Massot, [*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean/) 2장 (Apache License 2.0)
- 풀이 파일: [2026-10-11-박채원-lean-mathlib/](2026-10-11-박채원-lean-mathlib/) — 원본 연습문제의 `sorry` 자리에 답안과 한국어 주석 추가함

## 절별 정리

| 절 | 핵심 | 파일 |
| --- | --- | --- |
| 2.1 Calculating | 등식은 `rw` 로 바꿔 쓰고, 길면 `calc` 로 단계 나눔. 환 계산은 `ring` | [S01_Calculating.lean](2026-10-11-박채원-lean-mathlib/S01_Calculating.lean) |
| 2.2 Algebraic Structures | 환·군의 공리만으로 성질 증명. `have`, `apply`, `symm` | [S02_Proving_Identities_in_Algebraic_Structures.lean](2026-10-11-박채원-lean-mathlib/S02_Proving_Identities_in_Algebraic_Structures.lean) |
| 2.3 Theorems and Lemmas | 등식은 `rw`, 부등식은 `apply` / `exact`. 부등식 n개 잇기는 추이 정리 n−1번, `linarith` | [S03_Using_Theorems_and_Lemmas.lean](2026-10-11-박채원-lean-mathlib/S03_Using_Theorems_and_Lemmas.lean) |
| 2.4 Order and Divisibility | 등식 = `≤` 두 방향 (`le_antisymm`). min/max, `∣`, gcd. `repeat` | [S04_More_on_Order_and_Divisibility.lean](2026-10-11-박채원-lean-mathlib/S04_More_on_Order_and_Divisibility.lean) |
| 2.5 Algebraic Structures | 2.4 증명을 격자(⊓/⊔)·순서환·거리공간에서 다시 함. `trans` | [S05_Proving_Facts_about_Algebraic_Structures.md](2026-10-11-박채원-lean-mathlib/S05_Proving_Facts_about_Algebraic_Structures.md) |

## 작은 예제

같은 명제를 tactic 으로도, 정리를 직접 이어 붙인 한 줄로도 증명할 수 있음 (2.3).

```lean
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  exact lt_of_le_of_lt h₂ h₃

example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e :=
  lt_of_le_of_lt h₀ (lt_trans h₁ (lt_of_le_of_lt h₂ h₃))
```

## 실행 기록

| 대상 | 환경 | 결과 |
| --- | --- | --- |
| 2.1–2.5 풀이 | Lean v4.27.0 + Mathlib `v4.27.0` (`import MIL.Common` 대신 필요한 Mathlib tactic 직접 import) | 컴파일 에러 0 |

- 원본 MIL 저장소 Lean 버전은 v4.30.0.

## 우리 프로젝트에 적용할 점

- **길이**: 정리 이름을 알면 tactic 여러 줄을 정리 한 줄(term)로 줄일 수 있음 → 길이 감소.
- **비용**: `linarith`, `nlinarith`, `simp` 같은 자동화는 짧지만 탐색을 함. 쓸 정리를 직접 `apply`/`exact` 하면 heartbeat 를 줄일 여지가 있음.
- **버전 호환**: Mathlib 정리·클래스 이름은 버전마다 바뀜. 예) 2.5 순서환 가정이 최근 Mathlib 에서는 `[Ring R] [PartialOrder R] [IsStrictOrderedRing R]` 형태. 대회 세 버전(v4.25–v4.27)에서 모두 있는 이름을 써야 함.
