by
  classical
  intro d e f h
  have hd : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j : Fin 9 => if j = i then e j else d j) :=
    ((hrelation d e).mp h.1).2
  have he : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j : Fin 9 => if j = i then f j else e j) :=
    ((hrelation e f).mp h.2).2
  have hrepl (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    simp only [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
            (if j = i then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i <;> simp [hji] <;> ring
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq', Finset.mem_univ]
  have htotal (a b : Fin 9 → ℤ) :
      digits_to_num b = digits_to_num a +
        ∑ i : Fin 9, (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    simp only [hdigits_to_num]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ha : ∀ i : Fin 9,
      7 ∣ digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    intro i
    have hi := hd i
    rw [hrepl d e i] at hi
    exact hi
  have hb : ∀ i : Fin 9,
      7 ∣ digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
    intro i
    have hi := he i
    rw [hrepl e f i] at hi
    exact hi
  have hsum : 7 ∣ ∑ i : Fin 9,
      (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ)) := by
    apply Finset.dvd_sum
    intro i _
    exact ha i
  have hseven : (7 : ℤ) ∣ 7 * digits_to_num d := ⟨digits_to_num d, rfl⟩
  have hde : 7 ∣ digits_to_num d + digits_to_num e := by
    have hs := dvd_sub hsum hseven
    have heq :
        (∑ i : Fin 9,
          (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ))) -
            7 * digits_to_num d =
          digits_to_num d + digits_to_num e := by
      calc
        (∑ i : Fin 9,
          (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ))) -
            7 * digits_to_num d =
          2 * digits_to_num d +
            ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
              rw [Finset.sum_add_distrib]
              simp [Finset.card_fin] <;> ring
        _ = digits_to_num d + digits_to_num e := by
          rw [htotal d e]
          ring
    rw [heq] at hs
    exact hs
  have hprime : Prime (7 : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by decide)
  have hpow : ∀ n : ℕ, ¬(7 : ℤ) ∣ (10 : ℤ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ]
        intro hn
        rcases hprime.dvd_mul.mp hn with hn | hn
        · exact ih hn
        · norm_num at hn
  intro i
  have hprod : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have hz := dvd_sub (dvd_add (ha i) (hb i)) hde
    have heq :
        ((digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ)) +
          (digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ))) -
            (digits_to_num d + digits_to_num e) =
          (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
      ring
    rw [heq] at hz
    exact hz
  have hfd : 7 ∣ f i - d i :=
    (hprime.dvd_mul.mp hprod).resolve_right (hpow (i : ℕ))
  have hn : 7 ∣ -(f i - d i) := dvd_neg.mpr hfd
  convert hn using 1 <;> ring