import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MIL.Common

/-
# Mathematics in Lean 2.3 Using Theorems and Lemmas — 풀이와 개념 정리

출처
- 원문: Jeremy Avigad, Patrick Massot, *Mathematics in Lean*, 2.3 Using Theorems and Lemmas
  https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#using-theorems-and-lemmas
- 원본 코드: https://github.com/leanprover-community/mathematics_in_lean
  (`MIL/C02_Basics/S03_Using_Theorems_and_Lemmas.lean`, Apache License 2.0)
- 원본 연습문제의 `sorry` 자리에 답안 작성 및 개념 설명용 한국어 주석 추가함.
  문제·예제 문장과 영어 주석은 원본 그대로 유지함.
- 원본 저장소 Lean 버전: v4.30.0

## 핵심 개념: 등식은 rw, 부등식은 apply / exact
- 부등식 정리는 "가정 → 결론" 모양이다. 예: `le_trans : a ≤ b → b ≤ c → a ≤ c`
  → 정리는 함수처럼 쓸 수 있다. 가정을 넣으면 결론이 나온다.
- `exact 증명` : 증명이 목표와 **정확히 같은 모양**일 때 바로 끝낸다. 인자를 다 채워야 한다.
  예: `exact le_trans h₀ h₁`
- `apply 정리` : 정리의 **결론**을 목표에 맞추고, 채우지 못한 **가정**은 새 목표로 남긴다.
  Lean이 알 수 있는 건 알아서 채운다. 예: `apply le_trans` → 목표 `x ≤ ?`, `? ≤ z`
- 한 줄 요약: 필요한 게 다 있으면 `exact`, 결론만 맞으면 `apply`.
- `have` 는 반대로 가정 쪽에 새 사실을 추가한다. 실제 증명은 셋을 섞어 쓴다.
- `↔` 정리: `rw [exp_le_exp]` 로 바꿔 쓰거나, `.mp`(→) / `.mpr`(←) 로 한쪽만 꺼내 쓴다.
- 자동화: `linarith` (선형 부등식, 모르는 사실은 `linarith [사실]` 로 넘김), `norm_num` (숫자),
  `apply?` / `exact?` (쓸 정리를 Mathlib 에서 검색)
- 참고: https://lean4.dev/tactics/core/exact-apply
-/

variable (a b c d e : ℝ)
open Real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variable (h : a ≤ b) (h' : b ≤ c)

-- 정리에 인자를 하나씩 넣을 때마다 남는 타입이 줄어드는 것을 #check 로 확인
#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x

#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

-- Try this.
-- 가정 4개를 이으면 하나의 사슬:  a ≤ b < c ≤ d < e   (h₀, h₁, h₂, h₃)
-- 사슬의 왼쪽 고리부터 하나씩 떼어내며 목표를 줄인다.
--   시작                         목표 a < e
--   apply lt_of_le_of_lt h₀  →   목표 b < e   (a ≤ b 를 h₀ 으로 떼어냄)
--   apply lt_trans h₁        →   목표 c < e   (b < c 를 h₁ 으로 떼어냄)
--   exact lt_of_le_of_lt h₂ h₃ → 끝          (남은 c ≤ d, d < e 를 합쳐 c < e)
-- 가정이 4개면 3번, n개면 n - 1번 처리한다. 한 번 처리할 때마다 부등식 두 개가 하나로 합쳐지기 때문.
-- 어떤 정리를 쓸지는 이어 붙이는 두 부등식이 ≤ 인지 < 인지 보고 고른다.
--   ≤,≤ → le_trans   ≤,< → lt_of_le_of_lt   <,≤ → lt_of_lt_of_le   <,< → lt_trans
--   (하나라도 < 가 섞이면 결과는 <)
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀        -- 남은 목표: b < e
  apply lt_trans h₁              -- 남은 목표: c < e
  exact lt_of_le_of_lt h₂ h₃     -- c ≤ d < e 를 합쳐 c < e

-- 같은 사슬을 한 줄 증명 항으로 (인자를 다 넣으면 목표가 남지 않는다)
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e :=
  lt_of_le_of_lt h₀ (lt_trans h₁ (lt_of_le_of_lt h₂ h₃))

-- 같은 문제를 linarith 는 한 줄로 끝낸다.
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

section

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

end

-- exp 는 linarith 가 모르므로, 필요한 부등식(exp b ≤ exp c)을 직접 넘겨준다.
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_left : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_right : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_left : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_right

example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl

-- 바깥에서 안쪽으로: c + □ ≤ c + □ → exp □ ≤ exp □ → a + d ≤ a + e
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_right   -- 남은 목표: exp (a + d) ≤ exp (a + e)
  rw [exp_le_exp]          -- 남은 목표: a + d ≤ a + e
  apply add_le_add_right h₀

example : (0 : ℝ) < 1 := by norm_num

-- log 는 진수가 양수여야 하므로 먼저 0 < 1 + exp a 를 보인다.
example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by linarith [exp_pos a]
  apply log_le_log h₀
  apply add_le_add_right (exp_le_exp.mpr h)   -- 1 + exp a ≤ 1 + exp b

example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a

-- 빼는 쪽이 커지면 결과는 작아진다: exp a ≤ exp b 만 넘겨주면 linarith 가 처리
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  linarith [exp_le_exp.mpr h]

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2*a*b = 2*a*b + 0 := by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

-- |x| ≤ y 는 -y ≤ x 와 x ≤ y 두 개로 쪼갠다 (abs_le').
-- 각각 (a - b)^2 ≥ 0, (a + b)^2 ≥ 0 에서 나온다.
example : |a*b| ≤ (a^2 + b^2)/2 := by
  have h1 : 0 ≤ (a - b)^2 := pow_two_nonneg _
  have h2 : 0 ≤ (a + b)^2 := pow_two_nonneg _
  apply abs_le'.mpr
  constructor        -- 목표 둘: a*b ≤ (a^2+b^2)/2 , -(a*b) ≤ (a^2+b^2)/2
  · nlinarith [h1]   -- 제곱식을 펼쳐야 해서 비선형 버전 nlinarith 사용
  · nlinarith [h2]

#check abs_le'.mpr
