by
  classical
  intro d e f h
  have hd := ((hrelation d e).mp h.1).2
  have he := ((hrelation e f).mp h.2).2
  have hreplace (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * 10 ^ (i : ℕ) := by
    rw [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = i then b j else a j) * 10 ^ (j : ℕ)) =
          ∑ j : Fin 9, (a j * 10 ^ (j : ℕ) +
            if j = i then (b j - a j) * 10 ^ (j : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases q : j = i
        · subst j
          simp only [if_pos]
          ring
        · simp only [q, if_false, add_zero]
      _ = (∑ j : Fin 9, a j * 10 ^ (j : ℕ)) +
          (b i - a i) * 10 ^ (i : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hdiff (a b : Fin 9 → ℤ) :
      (∑ i : Fin 9, (b i - a i) * 10 ^ (i : ℕ)) =
        digits_to_num b - digits_to_num a := by
    rw [hdigits_to_num, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hde (i : Fin 9) :
      7 ∣ digits_to_num d + (e i - d i) * 10 ^ (i : ℕ) := by
    have q := hd i
    rw [hreplace d e i] at q
    exact q
  have hef (i : Fin 9) :
      7 ∣ digits_to_num e + (f i - e i) * 10 ^ (i : ℕ) := by
    have q := he i
    rw [hreplace e f i] at q
    exact q
  have hsum : 7 ∣ digits_to_num e + digits_to_num d := by
    have hs : 7 ∣ ∑ i : Fin 9,
        (digits_to_num d + (e i - d i) * 10 ^ (i : ℕ)) := by
      apply Finset.dvd_sum
      intro i _
      exact hde i
    have hs' : 7 ∣ 9 * digits_to_num d +
        ∑ i : Fin 9, (e i - d i) * 10 ^ (i : ℕ) := by
      simpa [Finset.sum_add_distrib, Finset.sum_const] using hs
    rw [hdiff d e] at hs'
    have hseven : 7 ∣ 7 * digits_to_num d := ⟨digits_to_num d, rfl⟩
    convert dvd_sub hs' hseven using 1 <;> ring
  have hprod (i : Fin 9) :
      7 ∣ (f i - d i) * 10 ^ (i : ℕ) := by
    have q := dvd_add (dvd_sub (hef i) hsum) (hde i)
    convert q using 1 <;> ring
  intro i
  have hn : ¬(7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by
    intro q
    have q' : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by
      norm_cast at q ⊢
    exact (by norm_num : ¬(7 : ℕ) ∣ 10)
      ((by decide : Nat.Prime 7).dvd_of_dvd_pow q')
  rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp (hprod i) with q | q
  · simpa only [neg_sub] using dvd_neg.mpr q
  · exact (hn q).elim