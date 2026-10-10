# MIL 2.5 Proving Facts about Algebraic Structures — sorry 답안과 이유

- 원문: Jeremy Avigad, Patrick Massot, *Mathematics in Lean*, [2.5 Proving Facts about Algebraic Structures](https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#proving-facts-about-algebraic-structures) (Apache License 2.0)
- 원본 코드: [`MIL/C02_Basics/S05_Proving_Facts_about_Algebraic_Structures.lean`](https://github.com/leanprover-community/mathematics_in_lean)
- 원본 연습문제의 `sorry` 자리 답안과 그렇게 쓴 이유만 정리함.

## 이번 절 한 줄 요약

2.4에서 실수 min/max로 했던 증명을 **추상 구조(격자, 순서환, 거리공간)** 에서 다시 함.
공리만 써서 증명하므로 실수뿐 아니라 집합(∩/∪), 자연수(gcd/lcm)에도 그대로 통함.

- `⊓` (inf) = min 역할, `⊔` (sup) = max 역할
- 쓰는 정리 이름만 바뀜: `min_le_left → inf_le_left`, `le_min → le_inf`, `le_max_left → le_sup_left`, `max_le → sup_le`

---

## 1. 격자 (Lattice)

### 1-1. `x ⊓ y = y ⊓ x`

```lean
example : x ⊓ y = y ⊓ x := by
  apply le_antisymm          -- 등식 → ≤ 두 방향으로 쪼갬
  repeat                     -- 두 방향이 x, y 만 바뀐 같은 모양 → 한 번만 씀
    apply le_inf             -- "둘 다보다 작으면 ⊓ 보다도 작다"
    · apply inf_le_right     -- x ⊓ y ≤ y
    apply inf_le_left        -- x ⊓ y ≤ x
```

**왜?** 2.4 `min a b = min b a` 풀이와 똑같음. 이름만 min → ⊓ 로 바꿈.

### 1-2. `x ⊓ y ⊓ z = x ⊓ (y ⊓ z)` (결합법칙)

```lean
example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf             -- 왼쪽이 x 보다도, y ⊓ z 보다도 작음을 보임
    · trans x ⊓ y            -- x ⊓ y ⊓ z ≤ x ⊓ y ≤ x : 중간 다리로 x ⊓ y
      apply inf_le_left
      apply inf_le_left
    apply le_inf
    · trans x ⊓ y            -- ... ≤ x ⊓ y ≤ y
      apply inf_le_left
      apply inf_le_right
    apply inf_le_right       -- ... ≤ z
  apply le_inf               -- 반대 방향도 같은 방식
  · apply le_inf
    · apply inf_le_left
    trans y ⊓ z
    apply inf_le_right
    apply inf_le_left
  trans y ⊓ z
  apply inf_le_right
  apply inf_le_right
```

**왜?** `x ⊓ y ⊓ z ≤ x` 는 한 번에 안 나옴 → 중간에 `x ⊓ y` 를 끼워서 두 단계로 감.
`trans 중간항` = `le_trans` 와 같은 역할인데 중간항을 직접 적어 줄 수 있어서 읽기 쉬움.

### 1-3. `x ⊔ y = y ⊔ x`, `x ⊔ y ⊔ z = x ⊔ (y ⊔ z)`

```lean
example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le             -- "둘 다 z 보다 작으면 ⊔ 도 z 보다 작다"
    · apply le_sup_right
    apply le_sup_left
```

**왜?** ⊓ 풀이에서 부등호 방향만 뒤집음. `le_inf ↔ sup_le`, `inf_le_left ↔ le_sup_left`.
결합법칙도 1-2 와 같은 구조 (`trans x ⊔ y`, `trans y ⊔ z` 로 중간 다리).

### 1-4. 흡수법칙

```lean
theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left        -- x ⊓ (...) ≤ x 는 바로
  apply le_inf               -- x ≤ x ⊓ (x ⊔ y) : x ≤ x 이고 x ≤ x ⊔ y
  · apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le             -- x ≤ x 이고 x ⊓ y ≤ x
    · apply le_refl
    apply inf_le_left
  apply le_sup_left          -- x ≤ x ⊔ (...) 는 바로
```

**왜?** 한쪽 방향은 정리 하나로 바로 끝남. 나머지 방향은 `le_inf` / `sup_le` 로 쪼개면 `x ≤ x`(`le_refl`)와 쉬운 부등식 하나가 남음.

---

## 2. 분배법칙: 한쪽이 성립하면 다른 쪽도 성립

```lean
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) :
    a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc,
    @inf_comm _ _ c a, absorb2, inf_comm]
```

**왜?** 오른쪽 `(a ⊔ b) ⊓ (a ⊔ c)` 를 가정 `h` 로 펼친 다음, 교환(`inf_comm`)으로 모양을 맞추고 흡수법칙(`absorb1`, `absorb2`)으로 줄여서 왼쪽과 같게 만듦.

- `@inf_comm _ _ (a ⊔ b)` : `inf_comm` 을 아무 데나 쓰지 말고 **`(a ⊔ b)` 가 앞에 있는 곳에만** 쓰라고 위치를 지정한 것.
- 두 번째 문제(⊓ ↔ ⊔ 역할을 바꾼 것)는 같은 순서로 `sup_comm`, `inf_assoc`, `absorb2/1` 로 바꿔 씀.

---

## 3. 순서환 (부등식 + 사칙연산)

```lean
example (h : a ≤ b) : 0 ≤ b - a := by
  exact sub_nonneg.mpr h     -- sub_nonneg : 0 ≤ b - a ↔ a ≤ b, 오른쪽 → 왼쪽이라 .mpr

example (h : 0 ≤ b - a) : a ≤ b := by
  exact sub_nonneg.mp h      -- 왼쪽 → 오른쪽이라 .mp

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := mul_nonneg (sub_nonneg.mpr h) h'  -- 0 ≤ b - a, 0 ≤ c → 곱도 0 이상
  rw [sub_mul] at h1         -- (b - a) * c = b * c - a * c 로 펼침
  exact sub_nonneg.mp h1     -- 0 ≤ b * c - a * c → a * c ≤ b * c
```

**왜?** `a ≤ b` 를 바로 다루기보다 **"차이가 0 이상"** (`0 ≤ b - a`)으로 바꾸면 `mul_nonneg` 같은 정리를 쓸 수 있음.
`↔` 정리는 `.mp`(왼→오), `.mpr`(오→왼)로 한 방향만 꺼내 씀 (2.3 내용).

---

## 4. 거리공간: 거리는 0 이상

```lean
example (x y : X) : 0 ≤ dist x y := by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]       -- 0 을 dist x x 로 바꿈
    apply dist_triangle      -- dist x x ≤ dist x y + dist y x (삼각부등식)
  linarith [dist_comm x y]   -- dist y x = dist x y 이므로 0 ≤ 2 * dist x y
```

**왜?** 공리에 "거리 ≥ 0" 이 없어서 만들어야 함.
`0 = dist x x ≤ dist x y + dist y x = 2 · dist x y` 흐름 → 마지막은 `linarith` 에 `dist_comm` 을 힌트로 넘겨서 끝냄.

---

## 새로 나온 것

| 이름 | 뜻 |
|---|---|
| `trans y` | 부등식 중간에 y 를 끼워 두 단계로 나눔 (`le_trans` 와 같음) |
| `@정리 _ _ 인자` | 암묵적 인자를 직접 채워 `rw` 위치를 지정 |
| `rw [...] at h` | 목표 말고 가정 h 를 바꿈 |
| `linarith [사실]` | 추가 사실을 힌트로 주고 선형 부등식 자동 해결 |
