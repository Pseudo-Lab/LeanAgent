import MIL.Common
import Mathlib.Data.Real.Basic

/-
# Mathematics in Lean 2.4 More on Order and Divisibility — 풀이와 개념 정리

출처
- 원문: Jeremy Avigad, Patrick Massot, *Mathematics in Lean*, 2.4 More examples using apply and rw
  https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#more-examples-using-apply-and-rw
- 원본 코드: https://github.com/leanprover-community/mathematics_in_lean
  (`MIL/C02_Basics/S04_More_on_Order_and_Divisibility.lean`, Apache License 2.0)
- 원본 연습문제의 `sorry` 자리에 답안 작성 및 개념 설명용 한국어 주석 추가함.
  문제·예제 문장과 영어 주석은 원본 그대로 유지함.
- 원본 저장소 Lean 버전: v4.30.0

## 핵심 개념
- **등식을 부등식 두 개로**: `le_antisymm : a ≤ b → b ≤ a → a = b`
  min/max 같은 등식은 `apply le_antisymm`으로 ≤ 두 방향을 각각 보인다.
- **min/max는 정의가 아니라 성질로 다룬다**
  - `min_le_left/right` : min 은 각각보다 작다
  - `le_min` : 둘 다보다 작으면 min 보다도 작다 (max 는 `le_max_left/right`, `max_le`)
- **나눗셈 `∣`** (`\mid` 입력, 키보드 | 아님): `dvd_trans`, `dvd_mul_left/right`, `dvd_add`
  gcd 는 `Nat.dvd_antisymm`(서로 나누면 같다)으로 등식을 만든다.
- 새 tactic
  - `show 명제` : 지금 목표를 명시해서 읽기 쉽게 함
  - `repeat` : 같은 tactic 묶음을 실패할 때까지 반복 (대칭인 두 목표에 유용)
  - `intro` : `∀ x y, ...` 목표에서 변수를 꺼내 옴
-/

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

-- min 과 같은 방식: max_le (둘 다 작으면 max 도 작다)
example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

-- 결합법칙: 양쪽 방향마다 "각 항보다 작다"를 le_min 으로 쪼개고 le_trans 로 잇는다.
example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right
    apply min_le_right
  apply le_min
  · apply le_min
    · apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left
  apply le_trans
  apply min_le_right
  apply min_le_right

-- min a b + c 는 a + c 보다도, b + c 보다도 작다.
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_left
    apply min_le_left
  apply add_le_add_left
  apply min_le_right

-- ≤ 는 aux. ≥ 는 양변에서 c 를 빼고 aux 를 (−c) 로 다시 쓰는 요령.
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_left
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]

#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

-- 삼각부등식을 a = (a - b) + b 에 적용한다.
example : |a| - |b| ≤ |a - b| := by
  have h := abs_add_le (a - b) b   -- |a - b + b| ≤ |a - b| + |b|
  rw [sub_add_cancel] at h          -- |a| ≤ |a - b| + |b|
  linarith
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

-- 합의 각 항이 x 로 나누어떨어지면 합도 나누어떨어진다 (dvd_add).
example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right   -- x ∣ x * z 이면 x ∣ y * (x * z)
      apply dvd_mul_right
    apply dvd_mul_left               -- x ∣ x ^ 2
  rw [pow_two]                       -- w ^ 2 = w * w
  apply dvd_mul_of_dvd_right
  exact h
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

-- gcd m n 과 gcd n m 이 서로를 나누면 같다. min 문제와 같은 구조.
example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left
end

end C02S04
