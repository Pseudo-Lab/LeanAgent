by
  intro d e f h i
  classical
  have hrepl (a b : Fin 9 → ℤ) (k : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = k then b j else a j) =
        digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by
    rw [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = k then b j else a j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9,
            (a j * (10 : ℤ) ^ (j : ℕ) +
              if j = k then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = k
        · simp [hj]
          ring
        · simp [hj]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq', Finset.mem_univ, k.is_lt]
  have hA : ∀ k : Fin 9,
      7 ∣ digits_to_num d + (e k - d k) * (10 : ℤ) ^ (k : ℕ) := by
    intro k
    rw [← hrepl d e k]
    exact ((hrelation d e).mp h.1).2 k
  have hB : ∀ k : Fin 9,
      7 ∣ digits_to_num e + (f k - e k) * (10 : ℤ) ^ (k : ℕ) := by
    intro k
    rw [← hrepl e f k]
    exact ((hrelation e f).mp h.2).2 k
  have hchange :
      digits_to_num e = digits_to_num d +
        ∑ k : Fin 9, (e k - d k) * (10 : ℤ) ^ (k : ℕ) := by
    rw [hdigits_to_num]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsum :
      7 ∣ ∑ k : Fin 9,
        (digits_to_num d + (e k - d k) * (10 : ℤ) ^ (k : ℕ)) := by
    apply Finset.dvd_sum
    intro k _
    exact hA k
  have hsum_eq :
      (∑ k : Fin 9,
        (digits_to_num d + (e k - d k) * (10 : ℤ) ^ (k : ℕ))) =
        digits_to_num e + 8 * digits_to_num d := by
    calc
      _ = (∑ _k : Fin 9, digits_to_num d) +
          ∑ k : Fin 9, (e k - d k) * (10 : ℤ) ^ (k : ℕ) := by
        rw [Finset.sum_add_distrib]
      _ = 9 * digits_to_num d +
          ∑ k : Fin 9, (e k - d k) * (10 : ℤ) ^ (k : ℕ) := by
        simp [Finset.sum_const, Finset.card_fin]
        <;> ring
      _ = digits_to_num e + 8 * digits_to_num d := by
        rw [hchange]
        ring
  have h8 : 7 ∣ digits_to_num e + 8 * digits_to_num d := by
    rw [← hsum_eq]
    exact hsum
  have hDE : 7 ∣ digits_to_num e + digits_to_num d := by
    have h7 : 7 ∣ 7 * digits_to_num d := ⟨digits_to_num d, rfl⟩
    have hz := dvd_sub h8 h7
    convert hz using 1 <;> ring
  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have hx := dvd_sub (hB i) hDE
    have hy := dvd_add hx (hA i)
    convert hy using 1 <;> ring
  rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp hp with hi | hi
  · have hn := dvd_neg.mpr hi
    convert hn using 1 <;> ring
  · have hi' : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by
      norm_cast at hi ⊢
      <;> simpa [Int.coe_nat_dvd_left] using hi
    have h710 : (7 : ℕ) ∣ 10 :=
      (by decide : (7 : ℕ).Prime).dvd_of_dvd_pow hi'
    norm_num at h710