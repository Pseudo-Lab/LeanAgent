# Warm-up 14 · 15 풀이

- 출처: [Lean Refactor Arena](https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena) Benchmark 탭 Warm-up 14, 15번 (PutnamBench)
- 평가 버전: v4.25.0, v4.26.0, v4.27.0

---

## 14. `putnam_1964_b2` — PutnamBench, 1,754 reference tokens

### 문제

원소가 n개인 유한집합 S의 부분집합 모음 P가 다음을 만족한다.
- P의 어떤 두 집합도 공통 원소를 가진다.
- P에 없는 부분집합을 하나 더 넣으면 위 성질이 깨진다.

이때 P의 원소 개수가 2ⁿ⁻¹ 임을 보여라.

```lean
import Mathlib
import Aesop

set_option maxHeartbeats 0

open Set Function Filter Topology

theorem putnam_1964_b2
(S : Type*) [Fintype S] [Nonempty S]
(P : Finset (Set S))
(hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅)
(hPS : ¬∃ T : Set S, T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅))
: (P.card = 2 ^ (Fintype.card S - 1)) := by
  sorry
```

### 해설

**핵심: 부분집합을 (T, Tᶜ) 짝으로 묶으면, P는 짝마다 정확히 하나씩 가진다.**

S의 원소 개수를 n이라 하면 부분집합은 모두 2ⁿ개임. 이를 T와 여집합 Tᶜ끼리 짝지으면 짝은 2ⁿ⁻¹개가 됨 (T ≠ Tᶜ 이므로 짝이 겹치지 않음).
따라서 "짝마다 최대 하나"(≤)와 "짝마다 최소 하나"(≥)를 보이면 |P| = 2ⁿ⁻¹ 이 됨.

**1. 공집합은 P에 없음**

교차 조건에서 같은 집합을 두 번 고르면 ∅ ∩ ∅ = ∅ 이므로 ∅ ∉ P.
∅ 의 짝은 S (= ∅ᶜ) 이고 둘은 서로소임. 이를 모든 짝으로 일반화한 것이 2번.

**2. 짝마다 최대 하나 (교차 조건) → |P| ≤ 2ⁿ⁻¹**

T ∩ Tᶜ = ∅ 이므로 T 와 Tᶜ 가 둘 다 P에 있으면 교차 조건에 어긋남.

**3. 짝마다 최소 하나 (극대 조건) → |P| ≥ 2ⁿ⁻¹**

X 와 Xᶜ 가 둘 다 P에 없다고 가정 (귀류법).
- X 를 P에 넣을 수 없으므로, P 안에 X 와 겹치지 않는 Y 가 있음 → Y ⊆ Xᶜ
- Xᶜ 도 넣을 수 없으므로, P 안에 Xᶜ 와 겹치지 않는 Z 가 있음 → Z ⊆ X
- 그러면 Y ∩ Z ⊆ Xᶜ ∩ X = ∅ 으로 Y, Z 는 서로소인데, 둘 다 P 안의 집합이므로 교차 조건에 모순.

**4. 결론**

≤ 와 ≥ 가 모두 성립하므로 |P| = 2ⁿ⁻¹ (2.4 의 `le_antisymm` 과 같은 구조).

### Lean 증명 (직접 작성, 대회 참조 증명 아님)

해설 번호를 주석으로 연결함. 해설 1(공집합)은 해설 2 에 포함되므로 따로 쓰지 않음.

```lean
import Mathlib
import Aesop

set_option maxHeartbeats 0

open Set Function Filter Topology

theorem putnam_1964_b2
(S : Type*) [Fintype S] [Nonempty S]
(P : Finset (Set S))
(hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅)
(hPS : ¬∃ T : Set S, T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅))
: (P.card = 2 ^ (Fintype.card S - 1)) := by
  classical
  -- [핵심] 모든 T 에 대해 "T ∈ P ↔ Tᶜ ∉ P" : 짝 (T, Tᶜ) 마다 정확히 하나
  have key : ∀ T : Set S, T ∈ P ↔ Tᶜ ∉ P := by
    intro T
    constructor
    -- [해설 2] 짝마다 최대 하나: T ∩ Tᶜ = ∅ 이라 둘 다 있으면 교차 조건(hPP)에 모순
    · intro hT hTc
      exact hPP T hT Tᶜ hTc (Set.inter_compl_self T)
    -- [해설 3] 짝마다 최소 하나: T, Tᶜ 가 둘 다 없다고 가정 (귀류법)
    · intro hTc
      by_contra hT
      -- 극대 조건(hPS): T 를 넣을 수 없으니 T 와 겹치지 않는 U ∈ P 가 있음 (U = 해설의 Y)
      obtain ⟨U, hU, hTU⟩ : ∃ U ∈ P, T ∩ U = ∅ := by
        by_contra h
        exact hPS ⟨T, hT, fun U hU hTU => h ⟨U, hU, hTU⟩⟩
      -- Tᶜ 도 넣을 수 없으니 Tᶜ 와 겹치지 않는 V ∈ P 가 있음 (V = 해설의 Z)
      obtain ⟨V, hV, hTV⟩ : ∃ V ∈ P, Tᶜ ∩ V = ∅ := by
        by_contra h
        exact hPS ⟨Tᶜ, hTc, fun V hV hTV => h ⟨V, hV, hTV⟩⟩
      -- U ∩ V = ∅ 을 보이면 교차 조건(hPP)에 모순
      apply hPP U hU V hV
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hxU hxV
      by_cases hx : x ∈ T
      · -- x ∈ T 이면 x ∈ T ∩ U = ∅ : 모순 (U ⊆ Tᶜ)
        have : x ∈ T ∩ U := ⟨hx, hxU⟩
        rw [hTU] at this
        exact this
      · -- x ∉ T 이면 x ∈ Tᶜ ∩ V = ∅ : 모순 (V ⊆ T)
        have : x ∈ Tᶜ ∩ V := ⟨hx, hxV⟩
        rw [hTV] at this
        exact this
  -- [해설 4] 개수 세기: P 와 {Tᶜ | T ∈ P} 는 겹치지 않고, 합치면 전체 부분집합
  have hdisj : Disjoint P (P.image compl) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT'
    exact (key U).mp hU hT
  have hunion : P ∪ P.image compl = Finset.univ := by
    ext T
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
    by_cases hT : T ∈ P
    · exact Or.inl hT
    · refine Or.inr ⟨Tᶜ, ?_, compl_compl T⟩
      by_contra h
      exact hT ((key T).mpr h)
  -- |P| + |P| = 2ⁿ (여집합을 취해도 개수는 같음)
  have hcard : P.card + P.card = 2 ^ Fintype.card S := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_image_of_injective _ compl_injective, Finset.card_univ,
      Fintype.card_set] at h
    omega
  -- n ≥ 1 (Nonempty) 이므로 n = m + 1 로 쓰고 2·|P| = 2^(m+1) → |P| = 2^m
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card S = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  rw [hn, pow_succ] at hcard
  rw [hn, Nat.add_sub_cancel]
  omega
```

- 검증: Lean v4.27.0 + Mathlib `v4.27.0`, 컴파일 에러 0
  (로컬에서는 `import Mathlib` 대신 `import Mathlib.Data.Fintype.Powerset` 로 확인)

### 대회 참조 증명과 다른 점

- "최소 하나", "최대 하나"를 따로 증명하지 않고 `key : T ∈ P ↔ Tᶜ ∉ P` 하나로 묶어 X, Xᶜ 쪽 반복 코드를 생략함.
- 극대 조건에서 집합을 꺼내고 모순을 만들 때 중간 단계(교환법칙, `U ⊆ Aᶜ`, `V ⊆ A`)를 거치지 않고 바로 처리함.
- 개수 세기는 일대일대응을 자동화로 증명하지 않고 Mathlib 정리(`card_image_of_injective`, `Fintype.card_set`)와 `omega` 로 끝냄.

---

## 15. `putnam_1995_a3` — PutnamBench, 4,085 reference tokens

### 문제

9자리 수 d = d₁d₂…d₉ 의 한 자리 dᵢ 만 eᵢ 로 바꾼 9자리 수 9개가 모두 7의 배수이다.
f = f₁f₂…f₉ 도 e 와 같은 관계이다 (e 의 한 자리만 fᵢ 로 바꾼 수 9개가 모두 7의 배수).

이때 모든 i 에 대해 dᵢ − fᵢ 가 7의 배수임을 보여라.

**문제 해석**

- 각 자릿수가 7의 배수라는 뜻이 아님. **d 에서 i번째 자리 하나만 eᵢ 로 바꿔 만든 수**가 7의 배수라는 뜻.
  - 1번째 자리만 바꾸기: **e₁**d₂…d₉, 2번째 자리만 바꾸기: d₁**e₂**d₃…d₉, …, 9번째: d₁…d₈**e₉**
  - 이 9개의 수가 모두 7의 배수 (`% 7 == 0`) 이면 "d 와 e 가 관련 있다 (d ~ e)" 라고 함.
- **바꾸는 경우의 수는 9개뿐임.** e 가 처음부터 정해져 있으므로 i번째 자리에는 항상 eᵢ 하나만 들어감. 자릿수(9개)마다 수 하나씩 → 정확히 9개. 0~9 를 모두 넣어 보는 것이 아님 (eᵢ = dᵢ 여도 됨).
- **모든 자리가 0~9**: 맨 앞자리도 0 가능. Lean 의 `relation` 도 모든 i 에 똑같이 `0 ≤ d i < 10` 만 요구함.
- 결론 dᵢ − fᵢ 는 −9 ~ 9 범위이므로, 결국 dᵢ = fᵢ 이거나 차이가 ±7 이라는 뜻.

**Lean 명제 읽기**

- `d : Fin 9 → ℤ` : 0~8번 자리에 숫자를 하나씩 주는 함수 = 9자리 수
- `digits_to_num dig = ∑ dig i * 10^i` : 자리 숫자 × 10^자리번호 를 모두 더함 → `i = 0` 이 일의 자리
- `fun j => if j = i then e j else d j` : i번째 자리만 e 로 바꾸고 나머지는 d 그대로인 수
- 결론 `7 ∣ d i - f i` : 모든 자리에서 dᵢ − fᵢ 가 7의 배수

```lean
import Mathlib
import Aesop

set_option maxHeartbeats 0

open Filter Topology Real

theorem putnam_1995_a3
(relation : (Fin 9 → ℤ) → (Fin 9 → ℤ) → Prop)
(digits_to_num : (Fin 9 → ℤ) → ℤ)
(hdigits_to_num : digits_to_num = fun dig => ∑ i : Fin 9, (dig i) * 10^i.1)
(hrelation : ∀ d e : (Fin 9 → ℤ), relation d e ↔ (∀ i : Fin 9, d i < 10 ∧ d i ≥ 0 ∧ e i < 10 ∧ e i ≥ 0) ∧ (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j))))
: ∀ d e f : (Fin 9 → ℤ), ((relation d e) ∧ (relation e f)) → (∀ i : Fin 9, 7 ∣ d i - f i) := by
  sorry
```

### 해설

**핵심: "자리 하나 바꾸기 = 자릿값 하나 더하기" 로 쓰고, 9개를 모두 더하면 D + E 가 7의 배수가 됨.**

기호: dᵢ, eᵢ, fᵢ 는 i번째 자리 숫자(0~9), D, E 는 d, e 를 9자리 수로 읽은 값. 자릿값은 10⁰(일의 자리) ~ 10⁸.

**1. 자리 하나 바꾼 수를 식으로 쓰기**

수는 "각 자리 숫자 × 자릿값" 을 모두 더한 것임.

- 123 = 1×100 + **2**×10 + 3×1
- 153 = 1×100 + **5**×10 + 3×1 (십의 자리만 2 → 5)
- 두 식을 빼면 백의 자리·일의 자리 항은 같아서 사라지고 십의 자리 항만 남음 → 153 − 123 = (5 − 2) × 10 = 30

일반화: i번째 자리만 dᵢ → eᵢ 로 바꾸면 그 자리 항만 dᵢ×10ⁱ → eᵢ×10ⁱ 로 바뀜.

> i번째 자리만 바꾼 수 = D + (eᵢ − dᵢ) × 10ⁱ

따라서 조건은
- d ~ e : 모든 i 에서 Aᵢ = D + (eᵢ − dᵢ)×10ⁱ 가 7의 배수 (9개)
- e ~ f : 모든 i 에서 Bᵢ = E + (fᵢ − eᵢ)×10ⁱ 가 7의 배수 (9개)

**2. A 9개를 모두 더하기 → D + E 는 7의 배수**

7의 배수끼리 더해도 7의 배수이므로 A₁ + … + A₉ 도 7의 배수. 합을 "D 부분" 과 "차이 부분" 으로 나눠 계산함.

3자리 예시 (d = 123, e = 456, 7의 배수 여부는 무시하고 모양만 확인):

| 바꾼 자리 | 바꾼 수 | = D + (차이) × 자릿값 |
| --- | --- | --- |
| 백의 자리 1→4 | 423 | 123 + (4−1)×100 = 123 + 300 |
| 십의 자리 2→5 | 153 | 123 + (5−2)×10 = 123 + 30 |
| 일의 자리 3→6 | 126 | 123 + (6−3)×1 = 123 + 3 |

- 합: 423 + 153 + 126 = 702
- D 부분: 123 이 3번 → 369
- 차이 부분: 300 + 30 + 3 = 333 = 456 − 123 = **E − D** (차이를 자릿값별로 모으면 "e 전체 − d 전체")
- 확인: 369 + 333 = 702

9자리에서는 바꾼 수가 9개이므로

> A₁ + … + A₉ = 9D + (E − D) = 8D + E → 7의 배수

8D + E = 7D + (D + E) 이고 7D 는 7의 배수이므로 **D + E 도 7의 배수**.
(9자리라서 9 − 1 = 8 = 7 + 1 이 되어 D + E 가 깔끔하게 남음.)

**3. 같은 자리 i 에서 Aᵢ + Bᵢ**

> Aᵢ + Bᵢ = (D + E) + (eᵢ − dᵢ)×10ⁱ + (fᵢ − eᵢ)×10ⁱ = (D + E) + (fᵢ − dᵢ)×10ⁱ

eᵢ 는 더해졌다 빠지면서 사라짐. Aᵢ + Bᵢ 와 D + E 가 모두 7의 배수이므로 그 차이인 **(fᵢ − dᵢ)×10ⁱ 도 7의 배수**.

**4. 10ⁱ 떼어내기**

10ⁱ = 2ⁱ × 5ⁱ 에는 7 이 없음 (7 과 10 은 서로소). 소수 7 이 (fᵢ − dᵢ)×10ⁱ 를 나누므로 **fᵢ − dᵢ 를 나눔** → dᵢ − fᵢ 도 7의 배수. ∎

### Lean 증명 (직접 작성, 대회 참조 증명 아님)

해설 번호를 주석으로 연결함.

```lean
import Mathlib
import Aesop

set_option maxHeartbeats 0

open Filter Topology Real

theorem putnam_1995_a3
(relation : (Fin 9 → ℤ) → (Fin 9 → ℤ) → Prop)
(digits_to_num : (Fin 9 → ℤ) → ℤ)
(hdigits_to_num : digits_to_num = fun dig => ∑ i : Fin 9, (dig i) * 10^i.1)
(hrelation : ∀ d e : (Fin 9 → ℤ), relation d e ↔ (∀ i : Fin 9, d i < 10 ∧ d i ≥ 0 ∧ e i < 10 ∧ e i ≥ 0) ∧ (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j))))
: ∀ d e f : (Fin 9 → ℤ), ((relation d e) ∧ (relation e f)) → (∀ i : Fin 9, 7 ∣ d i - f i) := by
  intro d e f ⟨hde, hef⟩ i
  -- "자리 하나 바꾼 수 9개가 7의 배수" 조건만 꺼냄 (0~9 범위 조건은 안 씀)
  obtain ⟨-, h1⟩ := (hrelation d e).mp hde
  obtain ⟨-, h2⟩ := (hrelation e f).mp hef
  subst hdigits_to_num
  -- [1단계] i번째 자리만 바꾼 수 = 원래 수 + (바뀐 숫자 − 원래 숫자) × 10^i
  have key : ∀ (x y : Fin 9 → ℤ) i, ∑ j, (if j = i then y j else x j) * 10 ^ j.1
      = ∑ j, x j * 10 ^ j.1 + (y i - x i) * 10 ^ i.1 := fun x y i => by
    rw [show (y i - x i) * 10 ^ i.1 = ∑ j, if j = i then (y j - x j) * 10 ^ j.1 else 0 by simp,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> [(subst h; ring); simp]
  simp only [key] at h1 h2
  -- [2단계] A 9개를 모두 더함: 7 ∣ 9D + (E − D)
  have hS := Finset.dvd_sum (s := .univ) fun j _ => h1 j
  simp only [Finset.sum_add_distrib, sub_mul, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hS
  -- [3단계] (fᵢ − dᵢ)·10^i = Aᵢ + Bᵢ − (9D + E − D) + 7D 는 7의 배수
  have h3 : 7 ∣ (f i - d i) * 10 ^ i.1 := by
    convert dvd_add (dvd_sub (dvd_add (h1 i) (h2 i)) hS) (dvd_mul_right 7 (∑ j, d j * 10 ^ j.1)) using 1
    push_cast; ring
  -- [4단계] 7 과 10^i 는 서로소 (7·3 + 10·(−2) = 1) → 10^i 를 떼어냄
  exact dvd_sub_comm.mp ((IsCoprime.pow_right ⟨3, -2, by norm_num⟩).dvd_of_dvd_mul_right h3)
```

- 검증: Lean v4.27.0 + Mathlib `v4.27.0`, 컴파일 에러 0
  (로컬에서는 `import Mathlib` 대신 필요한 모듈만 import 해서 확인)

### 대회 참조 증명과 다른 점

- "자리 하나 바꾼 수" 식을 d→e, e→f 각각 `calc` 로 두 번 증명하지 않고, 일반 x, y 에 대한 `key` 하나로 한 번만 증명해 `simp only [key]` 로 18개 조건에 한꺼번에 적용함.
- 3단계 조합을 `have` 를 여러 겹 쌓아 단계별로 빼고 더하지 않고, `ring` 등식 하나와 `dvd_add`·`dvd_sub` 한 줄로 처리함.
- 4단계에서 "7 은 소수이고 10ⁱ 를 나누지 않음" 을 따로 증명하지 않고 `IsCoprime` (7·3 + 10·(−2) = 1) 한 줄로 10ⁱ 를 떼어냄.
