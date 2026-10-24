by
  classical
  intro d e f h
  have hde : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j : Fin 9 => if j = i then e j else d j) :=
    ((hrelation d e).mp h.1).2
  have hef : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j : Fin 9 => if j = i then f j else e j) :=
    ((hrelation e f).mp h.2).2
  have hnum (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [hdigits_to_num]
    calc
      ∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ (j : ℕ) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
            (if j = i then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp
          ring
        · simp [hji]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          ∑ j : Fin 9, (if j = i then
            (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by simp
  have hdiff (a b : Fin 9 → ℤ) :
      digits_to_num b = digits_to_num a +
        ∑ i : Fin 9, (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [hdigits_to_num, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hd : ∀ i : Fin 9,
      7 ∣ digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    intro i
    rw [← hnum d e i]
    exact hde i
  have hf : ∀ i : Fin 9,
      7 ∣ digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
    intro i
    rw [← hnum e f i]
    exact hef i
  have hs₀ : 7 ∣ ∑ i : Fin 9,
      (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ)) := by
    apply Finset.dvd_sum
    intro i _
    exact hd i
  have hseven : (7 : ℤ) ∣ 7 * digits_to_num d :=
    ⟨digits_to_num d, rfl⟩
  have hs : 7 ∣ digits_to_num e + digits_to_num d := by
    have ht := dvd_sub hs₀ hseven
    have hde_num := hdiff d e
    convert ht using 1
    rw [Finset.sum_add_distrib]
    norm_num [Finset.sum_const, Finset.card_fin]
    linarith [hde_num]
  have hp : ∀ i : Fin 9,
      7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    intro i
    have ht := dvd_add (dvd_sub (hf i) hs) (hd i)
    convert ht using 1 <;> ring
  have hcancel : ∀ n : ℕ, ∀ x : ℤ,
      7 ∣ x * (10 : ℤ) ^ n → 7 ∣ x := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simpa using hx
    | succ n ihn =>
        intro x hx
        have hy : 7 ∣ (x * (10 : ℤ) ^ n) * 10 := by
          simpa [pow_succ, mul_assoc] using hx
        rcases hy with ⟨k, hk⟩
        apply ihn x
        refine ⟨5 * k - 7 * (x * (10 : ℤ) ^ n), ?_⟩
        calc
          x * (10 : ℤ) ^ n =
              5 * ((x * (10 : ℤ) ^ n) * 10) -
                7 * (7 * (x * (10 : ℤ) ^ n)) := by ring
          _ = 7 * (5 * k - 7 * (x * (10 : ℤ) ^ n)) := by
            rw [hk]
            ring
  intro i
  have hi : 7 ∣ f i - d i := hcancel (i : ℕ) (f i - d i) (hp i)
  have hneg : 7 ∣ -(f i - d i) := dvd_neg.mpr hi
  convert hneg using 1 <;> ring