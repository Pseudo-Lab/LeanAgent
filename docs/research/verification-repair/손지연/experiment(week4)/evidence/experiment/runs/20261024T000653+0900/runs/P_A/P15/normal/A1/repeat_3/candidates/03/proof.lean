by
  classical
  intro d e f h
  have hde := ((hrelation d e).mp h.1).2
  have hef := ((hrelation e f).mp h.2).2
  have hrepl (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
            if j = i then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp <;> ring
        · simp [hji]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          ∑ j : Fin 9, (if j = i then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
        simp
  have hdiff :
      digits_to_num e - digits_to_num d =
        ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [hdigits_to_num]
    calc
      (∑ i : Fin 9, e i * (10 : ℤ) ^ (i : ℕ)) -
          ∑ i : Fin 9, d i * (10 : ℤ) ^ (i : ℕ) =
          ∑ i : Fin 9, (e i * (10 : ℤ) ^ (i : ℕ) -
            d i * (10 : ℤ) ^ (i : ℕ)) := Finset.sum_sub_distrib.symm
      _ = ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hsum :
      7 ∣ ∑ i : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = i then e j else d j) := by
    apply Finset.dvd_sum
    intro i _
    exact hde i
  have hsum_eq :
      (∑ i : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = i then e j else d j)) =
        digits_to_num e + 8 * digits_to_num d := by
    calc
      (∑ i : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = i then e j else d j)) =
          ∑ i : Fin 9, (digits_to_num d +
            (e i - d i) * (10 : ℤ) ^ (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hrepl d e i
      _ = (∑ _i : Fin 9, digits_to_num d) +
          ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
        rw [Finset.sum_add_distrib]
      _ = digits_to_num e + 8 * digits_to_num d := by
        rw [← hdiff]
        simp [Finset.sum_const, Finset.card_fin] <;> ring
  have hcong : 7 ∣ digits_to_num e + digits_to_num d := by
    have hs : 7 ∣ digits_to_num e + 8 * digits_to_num d := by
      rwa [hsum_eq] at hsum
    have hz : (7 : ℤ) ∣ 7 * digits_to_num d := ⟨digits_to_num d, rfl⟩
    have ht := dvd_sub hs hz
    convert ht using 1 <;> ring
  intro i
  have ha := hde i
  have hb := hef i
  rw [hrepl d e i] at ha
  rw [hrepl e f i] at hb
  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have ht := dvd_add (dvd_sub hb hcong) ha
    convert ht using 1 <;> ring
  have hx : 7 ∣ f i - d i := by
    rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp hp with hx | hpow
    · exact hx
    · have hpow' : (7 : ℕ) ∣ 10 ^ (i : ℕ) := by
        exact_mod_cast hpow
      have hten : (7 : ℕ) ∣ 10 :=
        Nat.Prime.dvd_of_dvd_pow (by decide) hpow'
      norm_num at hten
  convert dvd_neg.mpr hx using 1 <;> ring