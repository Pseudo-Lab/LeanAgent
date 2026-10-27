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
    ring
  -- [4단계] 7 과 10^i 는 서로소 (7·3 + 10·(−2) = 1) → 10^i 를 떼어냄
  exact dvd_sub_comm.mp ((IsCoprime.pow_right ⟨3, -2, by norm_num⟩).dvd_of_dvd_mul_right h3)
