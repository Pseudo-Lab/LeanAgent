import MIL.Common
import Mathlib.Data.Real.Basic

/-
# Mathematics in Lean 2.1 Calculating — 풀이와 개념 정리

출처
- 원문: Jeremy Avigad, Patrick Massot, *Mathematics in Lean*, 2.1 Calculating
  https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#calculating
- 원본 코드: https://github.com/leanprover-community/mathematics_in_lean
  (`MIL/C02_Basics/S01_Calculating.lean`, Apache License 2.0)
- 원본 연습문제의 `sorry` 자리에 답안 작성 및 개념 설명용 한국어 주석 추가함.
  문제·예제 문장과 영어 주석은 원본 그대로 유지함.
- 원본 저장소 Lean 버전: v4.30.0

## 핵심 개념
- `rw [h]` : 등식 `h : A = B`로 목표 안의 `A`를 `B`로 바꾼다 (rewrite).
  양변이 똑같아지면 `rfl`로 자동 종료된다.
- `rw [← h]` : 등식을 거꾸로 사용해 `B`를 `A`로 바꾼다. (`←`는 `\l` 입력)
- 곱셈·덧셈은 왼쪽부터 묶인다: `a * b * c` = `(a * b) * c`.
- `mul_comm x y : x * y = y * x`      (곱셈 교환법칙)
- `mul_assoc x y z : x * y * z = x * (y * z)`  (곱셈 결합법칙)
  → 괄호 방향은 정리에 고정되어 있다. 정방향은 "왼쪽 묶음 → 오른쪽 묶음",
    반대로 옮기고 싶으면 `← mul_assoc`.
- 인자를 넣으면 바꿀 위치를 지정하고, 생략하면 처음 맞는 패턴에 적용된다.
- `rw [h] at hyp` : 목표 대신 가정 `hyp`를 바꾼다.
- `nth_rw n [h]` : 패턴이 여러 번 나올 때 n번째 것만 바꾼다.
- `ring` : 교환 (반)환에서 성립하는 등식을 자동으로 증명하는 tactic.
  - 어떻게 하나: 양변을 각각 하나의 정해진 모양(정규형, normal form)으로 전개·정리한 뒤
    두 결과가 똑같은지 비교한다. 정규형은 항을 정해진 순서로 늘어놓은 다항식이라,
    같은 식이면 반드시 같은 모양이 나온다.
    예: (a + b) * (a - b) 와 a^2 - b^2 는 둘 다 a^2 - b^2 로 정리되므로 같다.
  - 공리(axiom)가 아니다: 새로 가정하는 것은 없고, 정리하는 과정에서 교환·결합·분배법칙을
    실제로 적용한 증명을 만들어 Lean 커널이 검사한다. 즉 `rw [mul_comm ..]`, `rw [mul_assoc ..]`
    를 사람 대신 전부 해 주는 것.
  - 다룰 수 있는 것: +, *, 뺄셈·음수(환일 때), 자연수 지수(`^`), 유리수 계수.
    실수뿐 아니라 정수·다항식 등 교환환이면 어디서나 쓸 수 있다.
  - 못 하는 것: `hyp : c = ...` 같은 가정은 보지 않는다 → 필요하면 `rw`로 먼저 대입.
    교환법칙이 없는 곳(행렬 곱 등)에서는 쓸 수 없다.
  - 참고: Mathlib `Mathlib/Tactic/Ring/Basic.lean`. 알고리즘은 Grégoire & Mahboubi,
    "Proving Equalities in a Commutative Ring Done Right in Coq" (2005)에 기반.
- `calc` : 계산 과정을 사람이 쓰듯 단계별로 적는다. `_`는 윗줄의 오른쪽 식.
-/

-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
-- (c * b) * a → (b * c) * a → b * (c * a) → b * (a * c)
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]      -- 교환: c * b → b * c
  rw [mul_assoc b c a]   -- 결합: (b * c) * a → b * (c * a)
  rw [mul_comm c a]      -- 교환: c * a → a * c

-- a * (b * c) 에는 `a * b`가 없어서 바로 `mul_comm a b`를 쓸 수 없다.
-- 먼저 ← mul_assoc 으로 괄호를 왼쪽으로 옮겨 `a * b`가 보이게 만든다.
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c] -- a * (b * c) → (a * b) * c
  rw [mul_comm a b]      -- (a * b) * c → (b * a) * c
  rw [mul_assoc b a c]   -- (b * a) * c → b * (a * c)

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
-- 인자 없이: mul_comm 은 가장 바깥 곱 a * (b * c) 를 (b * c) * a 로 바꾼다.
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]          -- a * (b * c) → (b * c) * a
  rw [mul_assoc]         -- (b * c) * a → b * (c * a)

-- 인자 하나만: mul_comm a 는 "a * ? = ? * a" 꼴만 찾는다.
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]       -- (a * b) * c
  rw [mul_comm a]        -- (b * a) * c
  rw [mul_assoc]         -- b * (a * c)

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

-- 가정 h 를 쓰려면 목표 안에 `b * c` 가 한 덩어리로 보여야 한다.
-- ((a * b) * c) * d 에서 mul_assoc a 로 (a * (b * c)) * d 를 만든다.
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]       -- (a * (b * c)) * d
  rw [h]                 -- (a * (e * f)) * d
  rw [← mul_assoc]       -- ((a * e) * f) * d

-- 가정을 대입해 b * a - a * b 를 만든 뒤 0 으로 만든다.
example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]               -- b * a - d = 0
  rw [hyp']              -- b * a - a * b = 0
  rw [mul_comm]          -- a * b - a * b = 0
  rw [sub_self]          -- sub_self x : x - x = 0

-- 여러 rw 를 한 줄에 쓸 수도 있다.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

-- variable 로 변수를 한 번 선언하면 아래 example 들에서 다시 쓰지 않아도 된다.
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

-- #check : 식이나 정리의 타입(= 무슨 내용인지)을 Infoview 에 보여준다.
#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

-- calc 의 각 단계를 직접 채우기
-- mul_add : x * (y + z) = x * y + x * z   (분배법칙, 왼쪽)
-- add_mul : (x + y) * z = x * z + y * z   (분배법칙, 오른쪽)
-- two_mul : 2 * x = x + x
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

-- 분배법칙을 펼친 뒤 덧셈 괄호를 왼쪽으로 정리한다.
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [add_mul, mul_add, mul_add]  -- a * c + a * d + (b * c + b * d)
  rw [← add_assoc]                -- (a * c + a * d + b * c) + b * d

-- (a + b) * (a - b) 를 펼치면 a*a - a*b + (b*a - b*b).
-- a*b 와 b*a 를 맞춰 상쇄시키고 a*a 를 a^2 로 바꾼다.
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [add_mul, mul_sub, mul_sub]  -- a * a - a * b + (b * a - b * b)
  rw [add_sub]                    -- a * a - a * b + b * a - b * b   (add_sub : x + (y - z) = x + y - z)
  rw [mul_comm b a]               -- a * a - a * b + a * b - b * b
  rw [sub_add_cancel]             -- a * a - b * b                   (sub_add_cancel : x - y + y = x)
  rw [pow_two, pow_two]           -- pow_two : x ^ 2 = x * x

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

-- 가정을 바꿔서 목표와 똑같이 만든 뒤 exact 로 닫는다.
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

-- ring 은 위의 rw 연쇄를 한 번에 처리한다.
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

-- ring 은 가정을 못 쓰므로 rw 로 먼저 대입한다.
example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

-- nth_rw 2 [h] : (a + b) 가 두 번 나오는데 두 번째 것만 c 로 바꾼다.
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]           -- (a + b) * c
  rw [add_mul]           -- a * c + b * c
