by
  classical
  intro d e f h
  have hde : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j : Fin 9 => if j = i then e j else d j) :=
    ((hrelation d e).mp h.1).2
  have hef : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j : Fin 9 => if j = i then f j else e j) :=
    ((hrelation e f).mp h.2).2
  have replace (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    simp only [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
            if j = i then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : j = i
        · subst j
          simp
          <;> ring
        · simp [hij]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          ∑ j : Fin 9, if j = i then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by simp
  have num_sub (a b : Fin 9 → ℤ) :
      digits_to_num b - digits_to_num a =
        ∑ i : Fin 9, (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    simp only [hdigits_to_num]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hde' (i : Fin 9) :
      7 ∣ digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [← replace d e i]
    exact hde i
  have hef' (i : Fin 9) :
      7 ∣ digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [← replace e f i]
    exact hef i
  have hsum :
      7 ∣ ∑ i : Fin 9,
        (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ)) := by
    apply Finset.dvd_sum
    intro i _
    exact hde' i
  have hsum_eq :
      (∑ i : Fin 9,
        (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ))) =
          (digits_to_num e + digits_to_num d) + 7 * digits_to_num d := by
    calc
      _ = (∑ _i : Fin 9, digits_to_num d) +
          ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
        rw [Finset.sum_add_distrib]
      _ = 9 * digits_to_num d +
          ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
        simp [Finset.sum_const, Finset.card_fin]
        <;> ring
        <;> norm_num
      _ = (digits_to_num e + digits_to_num d) + 7 * digits_to_num d := by
        rw [← num_sub d e]
        ring
  have hnums : 7 ∣ digits_to_num e + digits_to_num d := by
    rw [hsum_eq] at hsum
    have hseven : 7 ∣ 7 * digits_to_num d := ⟨digits_to_num d, rfl⟩
    have hrest := dvd_sub hsum hseven
    convert hrest using 1 <;> ring
  intro i
  have hprod : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have hleft := dvd_sub (hef' i) hnums
    have hadd := dvd_add hleft (hde' i)
    convert hadd using 1 <;> ring
  have hpow : ¬(7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by
    intro hi
    have hin : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by
      exact_mod_cast hi
    have hten : (7 : ℕ) ∣ 10 :=
      (by decide : Nat.Prime 7).dvd_of_dvd_pow hin
    norm_num at hten
  have hor :
      (7 : ℤ) ∣ (f i - d i) ∨ (7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by
    apply (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp
    exact hprod
  have hfd : (7 : ℤ) ∣ f i - d i := hor.resolve_right hpow
  simpa only [neg_sub] using (dvd_neg.mpr hfd)