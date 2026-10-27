import Mathlib
import Aesop

set_option maxHeartbeats 0

open Filter Topology Real


theorem putnam_1995_a3
(relation : (Fin 9 → ℤ) → (Fin 9 → ℤ) → Prop)
(digits_to_num : (Fin 9 → ℤ) → ℤ)
(hdigits_to_num : digits_to_num = fun dig => ∑ i : Fin 9, (dig i) * 10^i.1)
(hrelation : ∀ d e : (Fin 9 → ℤ), relation d e ↔ (∀ i : Fin 9, d i < 10 ∧ d i ≥ 0 ∧ e i < 10 ∧ e i ≥ 0) ∧ (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j))))
: ∀ d e f : (Fin 9 → ℤ), ((relation d e) ∧ (relation e f)) → (∀ i : Fin 9, 7 ∣ d i - f i) := by
  classical
  have hreplace (a b : Fin 9 → ℤ) (k : Fin 9) :
      digits_to_num (fun j => if j = k then b j else a j) =
        digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by
    simp only [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = k then b j else a j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
            (if j = k then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = k
        · simp [hj]
          ring
        · simp [hj]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hdiff (a b : Fin 9 → ℤ) :
      digits_to_num b = digits_to_num a +
        ∑ k : Fin 9, (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by
    simp only [hdigits_to_num]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsum (a b : Fin 9 → ℤ) (hab : relation a b) :
      7 ∣ digits_to_num a + digits_to_num b := by
    have hr := ((hrelation a b).mp hab).2
    have hs : 7 ∣ ∑ k : Fin 9,
        (digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ)) := by
      apply Finset.dvd_sum
      intro k _
      rw [← hreplace a b k]
      exact hr k
    have heq :
        (∑ k : Fin 9, (digits_to_num a +
          (b k - a k) * (10 : ℤ) ^ (k : ℕ))) =
          9 * digits_to_num a +
            ∑ k : Fin 9, (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by
      rw [Finset.sum_add_distrib]
      simp
    rw [heq] at hs
    have ht : 7 ∣ 8 * digits_to_num a + digits_to_num b := by
      rw [hdiff a b]
      convert hs using 1 <;> ring
    have hseven : 7 ∣ 7 * digits_to_num a := ⟨digits_to_num a, rfl⟩
    convert dvd_sub ht hseven using 1 <;> ring
  intro d e f h i
  have hde := ((hrelation d e).mp h.1).2 i
  have hef := ((hrelation e f).mp h.2).2 i
  rw [hreplace d e i] at hde
  rw [hreplace e f i] at hef
  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have ht := dvd_sub (dvd_add hde hef) (hsum d e h.1)
    convert ht using 1 <;> ring
  have hfd : 7 ∣ f i - d i := by
    rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp hp with hp | hp
    · exact hp
    · exfalso
      have hp' : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by
        norm_cast at hp ⊢
      have hbad : (7 : ℕ) ∣ 10 :=
        Nat.Prime.dvd_of_dvd_pow (by decide) hp'
      norm_num at hbad
  simpa only [neg_sub] using (dvd_neg.mpr hfd)
