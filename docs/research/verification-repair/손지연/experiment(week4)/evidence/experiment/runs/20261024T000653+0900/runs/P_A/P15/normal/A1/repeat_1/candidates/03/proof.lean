by
  classical
  have hchange (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    simp only [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
            (if j = i then (b i - a i) * (10 : ℤ) ^ (j : ℕ) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp
          <;> ring
        · simp [hji]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp
  have hdiff (a b : Fin 9 → ℤ) :
      (∑ i : Fin 9, (b i - a i) * (10 : ℤ) ^ (i : ℕ)) =
        digits_to_num b - digits_to_num a := by
    simp only [hdigits_to_num]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum (a b : Fin 9 → ℤ)
      (hab : ∀ i : Fin 9,
        7 ∣ digits_to_num (fun j : Fin 9 => if j = i then b j else a j)) :
      7 ∣ digits_to_num a + digits_to_num b := by
    have hs : 7 ∣ ∑ i : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = i then b j else a j) := by
      apply Finset.dvd_sum
      intro i _
      exact hab i
    have hid : (∑ i : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = i then b j else a j)) =
        8 * digits_to_num a + digits_to_num b := by
      calc
        (∑ i : Fin 9,
            digits_to_num (fun j : Fin 9 => if j = i then b j else a j)) =
            ∑ i : Fin 9, (digits_to_num a +
              (b i - a i) * (10 : ℤ) ^ (i : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hchange a b i
        _ = 9 * digits_to_num a +
            ∑ i : Fin 9, (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
          rw [Finset.sum_add_distrib]
          simp [Finset.sum_const, Finset.card_fin]
          <;> ring
        _ = 8 * digits_to_num a + digits_to_num b := by
          rw [hdiff a b]
          ring
    rw [hid] at hs
    have hseven : 7 ∣ 7 * digits_to_num a := ⟨digits_to_num a, rfl⟩
    have ht := dvd_sub hs hseven
    convert ht using 1 <;> ring
  intro d e f h
  have hde := (hrelation d e).mp h.1
  have hef := (hrelation e f).mp h.2
  have hs : 7 ∣ digits_to_num d + digits_to_num e := hsum d e hde.2
  intro i
  have ha := hde.2 i
  have hb := hef.2 i
  rw [hchange d e i] at ha
  rw [hchange e f i] at hb
  have hprod : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have ht := dvd_sub (dvd_add ha hb) hs
    convert ht using 1 <;> ring
  rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp hprod with hfd | hpow
  · have hneg : 7 ∣ -(f i - d i) := dvd_neg.mpr hfd
    convert hneg using 1 <;> ring
  · exfalso
    have hpow' : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by
      norm_cast at hpow ⊢
      simpa [Int.coe_nat_dvd_left] using hpow
    have hten : (7 : ℕ) ∣ 10 :=
      Nat.Prime.dvd_of_dvd_pow (by decide) hpow'
    norm_num at hten