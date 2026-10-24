by
  have hdiff (a b : Fin 9 → ℤ) :
      digits_to_num b = digits_to_num a +
        ∑ j : Fin 9, (b j - a j) * (10 : ℤ) ^ (j : ℕ) := by
    rw [hdigits_to_num, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrepl (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    calc
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
          digits_to_num a + ∑ j : Fin 9,
            ((if j = i then b j else a j) - a j) * (10 : ℤ) ^ (j : ℕ) :=
        hdiff a (fun j : Fin 9 => if j = i then b j else a j)
      _ = digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
        congr 1
        calc
          ∑ j : Fin 9, ((if j = i then b j else a j) - a j) *
              (10 : ℤ) ^ (j : ℕ) =
              ∑ j : Fin 9, if j = i then
                (b i - a i) * (10 : ℤ) ^ (i : ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases h : j = i
            · subst j
              simp
            · simp [h]
          _ = (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by simp
  rintro d e f ⟨rde, ref⟩
  have hde (i : Fin 9) :
      7 ∣ digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [← hrepl d e i]
    exact ((hrelation d e).mp rde).2 i
  have hef (i : Fin 9) :
      7 ∣ digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [← hrepl e f i]
    exact ((hrelation e f).mp ref).2 i
  have hs : 7 ∣ ∑ i : Fin 9,
      (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ)) := by
    apply Finset.dvd_sum
    intro i _
    exact hde i
  have hid :
      (∑ i : Fin 9, (digits_to_num d +
        (e i - d i) * (10 : ℤ) ^ (i : ℕ))) =
        digits_to_num d + digits_to_num e + 7 * digits_to_num d := by
    rw [hdiff d e, Finset.sum_add_distrib]
    simp [Finset.sum_const]
    ring
  have hsum : 7 ∣ digits_to_num d + digits_to_num e := by
    rw [hid] at hs
    have h7 : (7 : ℤ) ∣ 7 * digits_to_num d := ⟨digits_to_num d, rfl⟩
    convert dvd_sub hs h7 using 1 <;> ring
  intro i
  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have h := dvd_sub (dvd_add (hde i) (hef i)) hsum
    convert h using 1 <;> ring
  rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp hp with h | h
  · convert dvd_neg.mpr h using 1 <;> ring
  · have hn : (7 : ℕ) ∣ 10 ^ (i : ℕ) := by
      exact_mod_cast h
    have hten := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 7) hn
    norm_num at hten