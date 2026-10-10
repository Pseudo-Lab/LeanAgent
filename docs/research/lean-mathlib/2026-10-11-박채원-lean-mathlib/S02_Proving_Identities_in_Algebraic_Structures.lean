import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

/-
# Mathematics in Lean 2.2 Proving Identities in Algebraic Structures — 풀이와 개념 정리

출처
- 원문: Jeremy Avigad, Patrick Massot, *Mathematics in Lean*, 2.2 Proving Identities in Algebraic Structures
  https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#proving-identities-in-algebraic-structures
- 원본 코드: https://github.com/leanprover-community/mathematics_in_lean
  (`MIL/C02_Basics/S02_Proving_Identities_in_Algebraic_Structures.lean`, Apache License 2.0)
- 원본 연습문제의 `sorry` 자리에 답안 작성 및 개념 설명용 한국어 주석 추가함.
  문제·예제 문장과 영어 주석은 원본 그대로 유지함.
- 원본 저장소 Lean 버전: v4.30.0

## 핵심 개념
- 2.1에서는 실수(ℝ) 위에서 계산했다면, 2.2는 **임의의 환(ring) R** 위에서 증명한다.
  `variable (R : Type*) [Ring R]` = "R은 어떤 타입이고, 환 구조를 가진다"는 가정.
  이렇게 증명하면 정수·실수·행렬 등 **모든 환에 한 번에** 적용된다.
- 환의 공리(axiom): `add_assoc`, `add_comm`, `zero_add`, `neg_add_cancel`(-a + a = 0),
  `mul_assoc`, `mul_one`, `one_mul`, `mul_add`, `add_mul`.
  이 절의 목표는 **공리만 가지고** `a + 0 = a`, `a * 0 = 0`, `- -a = a` 같은
  "당연해 보이는" 성질을 직접 증명해 보는 것. (Mathlib에는 이미 있는 정리들)
- `[Ring R]` vs `[CommRing R]`: 곱셈 교환법칙이 있는 환이 CommRing.
  `ring` tactic은 CommRing에서만 쓸 수 있다.
- `namespace MyRing ... end MyRing`: 이름 충돌을 피하려고 만든 이름 공간.
  안에서 만든 `add_zero`의 전체 이름은 `MyRing.add_zero`라서 Mathlib의 `add_zero`와 겹치지 않는다.
- `{a b : R}` (중괄호) = 암묵적 인자: 가정 `h`에서 Lean이 알아서 추론하므로 직접 쓰지 않는다.
  `(a b : R)` (소괄호) = 명시적 인자: 쓸 때 직접 넣어야 한다. 예: `neg_add_cancel_left a b`
- 새로 쓰는 tactic
  - `have h : 명제 := by ...` : 중간 결과(보조 사실)를 먼저 증명해 두고 이름 붙이기
  - `apply 정리` : 목표가 정리의 결론과 맞으면, 정리의 가정을 새 목표로 바꾼다 (거꾸로 추론)
  - `symm` : 등식 목표의 양변을 바꾼다 (a = b → b = a)
  - `rfl` : 양변이 정의상 같으면 바로 닫는다
  - `norm_num` : 숫자 계산(1 + 1 = 2 등)을 자동 처리
- 마지막 부분은 같은 생각을 **군(group)**에 적용한다.
  군의 공리는 `mul_assoc`, `one_mul`(1 * a = a), `inv_mul_cancel`(a⁻¹ * a = 1) 세 개뿐이고,
  오른쪽 버전(`a * a⁻¹ = 1`, `a * 1 = a`)은 공리가 아니라 **증명해야 하는 정리**다.
-/

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

-- CommRing 이면 실수 때처럼 ring 을 그대로 쓸 수 있다.
example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
-- (a + b) + -b → a + (b + -b) → a + 0 → a
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc]         -- a + (b + -b)
  rw [add_neg_cancel]    -- a + 0
  rw [add_zero]          -- a

-- 양변 왼쪽에 -a 를 더한 것과 같은 효과: b = -a + (a + b) = -a + (a + c) = c
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b]  -- 목표 왼쪽 b 를 -a + (a + b) 로 바꿈
  rw [h]                          -- -a + (a + c) = c
  rw [neg_add_cancel_left]        -- c = c

-- 오른쪽 버전: a = (a + b) + -b = (c + b) + -b = c
theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b]
  rw [h]
  rw [add_neg_cancel_right]

-- 아이디어: a * 0 + a * 0 = a * (0 + 0) = a * 0 = a * 0 + 0 이므로 소거법칙으로 a * 0 = 0
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

-- mul_zero 와 같은 방법을 왼쪽에서: 0 * a + 0 * a = (0 + 0) * a
theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

-- -a = -a + (a + b) = -a + 0 ... 을 거꾸로: -a 를 -a + (a + b) 로 바꾼 뒤 h 로 a + b = 0
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b]  -- -a = -a + (a + b)
  rw [h]                          -- -a = -a + 0
  rw [add_zero]                   -- -a = -a

-- 바로 위 정리를 재사용한다. symm 으로 양변을 바꿔 "-b = a" 꼴로 만든 뒤 apply.
theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  symm                            -- -b = a
  apply neg_eq_of_add_eq_zero     -- 남은 목표: b + a = 0
  rw [add_comm, h]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

-- - -a = a 를 "neg_eq_of_add_eq_zero" 꼴로 보면, -a + a = 0 만 보이면 된다.
theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero     -- 남은 목표: -a + a = 0
  rw [neg_add_cancel]

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

-- 일반 환에서 뺄셈은 "음수를 더하는 것"이라는 정리로 바꿔 쓴다.
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

-- 실수에서는 뺄셈이 애초에 그렇게 정의되어 있어서 rfl 로 바로 닫힌다.
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

-- a - a → a + -a → 0
theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg]    -- a + -a = 0
  rw [add_neg_cancel]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

-- 2 * a → (1 + 1) * a → 1 * a + 1 * a → a + a
theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two]  -- (1 + 1) * a = a + a
  rw [add_mul]               -- 1 * a + 1 * a = a + a
  rw [one_mul]               -- a + a = a + a

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

-- 군에서는 왼쪽 역원(a⁻¹ * a = 1)만 공리다. 오른쪽(a * a⁻¹ = 1)은 증명해야 한다.
-- 요령: x = a * a⁻¹ 라 두면 x * x = x 임을 보이고, 양변 왼쪽에 x⁻¹ 를 곱하면 x = 1.
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
  rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]

-- 1 을 a⁻¹ * a 로 바꾼 뒤, 위에서 증명한 mul_inv_cancel 을 쓴다.
theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a]  -- a * (a⁻¹ * a) = a
  rw [← mul_assoc]         -- a * a⁻¹ * a = a
  rw [mul_inv_cancel]      -- 1 * a = a
  rw [one_mul]

-- (a * b)⁻¹ = b⁻¹ * a⁻¹ : 오른쪽에 1 = (a * b)⁻¹ * (a * b) 를 끼워 넣고 정리한다.
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹ * a⁻¹), ← inv_mul_cancel (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
    mul_inv_cancel, one_mul, mul_inv_cancel, mul_one]

end MyGroup

end
