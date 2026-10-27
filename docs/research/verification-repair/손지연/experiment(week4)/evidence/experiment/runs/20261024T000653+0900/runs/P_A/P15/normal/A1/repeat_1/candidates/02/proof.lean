by
  classical
  have hrepl (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    simp only [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
            if j = i then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i <;> simp [hji] <;> ring
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          ∑ j : Fin 9, if j = i then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
        simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hdelta (a b : Fin 9 → ℤ) :
      (∑ i : Fin 9, (b i - a i) * (10 : ℤ) ^ (i : ℕ)) =
        digits_to_num b - digits_to_num a := by
    simp only [hdigits_to_num]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum (a b : Fin 9 → ℤ)
      (hab : ∀ i : Fin 9,
        7 ∣ digits_to_num (fun j => if j = i then b j else a j)) :
      7 ∣ digits_to_num a + digits_to_num b := by
    have hs : 7 ∣ ∑ i : Fin 9,
        digits_to_num (fun j => if j = i then b j else a j) := by
      apply Finset.dvd_sum
      intro i _
      exact hab i
    simp only [hrepl] at hs
    have heq :
        (∑ i : Fin 9, (digits_to_num a +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ))) =
          8 * digits_to_num a + digits_to_num b := by
      rw [Finset.sum_add_distrib, hdelta a b]
      simp <;> ring
    rw [heq] at hs
    have hseven : 7 ∣ 7 * digits_to_num a := ⟨digits_to_num a, rfl⟩
    convert dvd_sub hs hseven using 1 <;> ring
  intro d e f h
  have hde : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j => if j = i then e j else d j) :=
    ((hrelation d e).mp h.1).2
  have hef : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j => if j = i then f j else e j) :=
    ((hrelation e f).mp h.2).2
  have hsde : 7 ∣ digits_to_num d + digits_to_num e := hsum d e hde
  intro i
  have ha : 7 ∣ digits_to_num d +
      (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    simpa only [hrepl] using hde i
  have hb : 7 ∣ digits_to_num e +
      (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
    simpa only [hrepl] using hef i
  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have ht := dvd_sub (dvd_add ha hb) hsde
    convert ht using 1 <;> ring
  fin_cases i <;> norm_num at hp ⊢ <;> omega