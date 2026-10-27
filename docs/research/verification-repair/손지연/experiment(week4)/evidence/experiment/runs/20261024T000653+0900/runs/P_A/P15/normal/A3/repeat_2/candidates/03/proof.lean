by
  have hreplace (x y : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j => if j = i then y j else x j) =
        digits_to_num x + (y i - x i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = i then y j else x j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9, (x j * (10 : ℤ) ^ (j : ℕ) +
            if j = i then (y j - x j) * (10 : ℤ) ^ (j : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp
          ring
        · simp [hji]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp
  have hpair (x y : Fin 9 → ℤ)
      (ha : ∀ i : Fin 9,
        7 ∣ digits_to_num (fun j : Fin 9 => if j = i then y j else x j)) :
      7 ∣ digits_to_num x + digits_to_num y := by
    have hs : 7 ∣ ∑ i : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = i then y j else x j) := by
      apply Finset.dvd_sum
      intro i _
      exact ha i
    convert dvd_sub hs
      (show (7 : ℤ) ∣ 7 * digits_to_num x from ⟨digits_to_num x, rfl⟩) using 1
    simp_rw [hreplace]
    simp [hdigits_to_num, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_const]
    ring
  intro d e f ⟨hde, hef⟩ i
  have hd := ((hrelation d e).mp hde).2
  have hf := ((hrelation e f).mp hef).2
  have hx := dvd_sub (dvd_add (hd i) (hf i)) (hpair d e hd)
  rw [hreplace d e i, hreplace e f i] at hx
  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    convert hx using 1
    ring
  rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp hp with hp | hp
  · convert dvd_neg.mpr hp using 1 <;> ring
  · have hp' : (7 : ℕ) ∣ 10 ^ (i : ℕ) := by
      norm_cast at hp ⊢
    have hten := Nat.Prime.dvd_of_dvd_pow (by decide) hp'
    norm_num at hten