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
  intro d e f h i
  have hdiff (a b : Fin 9 → ℤ) :
      digits_to_num b - digits_to_num a =
        ∑ j : Fin 9, (b j - a j) * (10 : ℤ) ^ (j : ℕ) := by
    rw [hdigits_to_num, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrepl (a b : Fin 9 → ℤ) (k : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = k then b j else a j) =
        digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by
    rw [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = k then b j else a j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
            if j = k then (b j - a j) * (10 : ℤ) ^ (j : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = k
        · subst j
          simp only [if_pos]
          ring
        · simp [hj]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hrepdvd (a b : Fin 9 → ℤ) (hab : relation a b) (k : Fin 9) :
      7 ∣ digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ) := by
    rw [← hrepl a b k]
    exact ((hrelation a b).mp hab).2 k
  have hsum (a b : Fin 9 → ℤ) (hab : relation a b) :
      7 ∣ digits_to_num a + digits_to_num b := by
    have hs : 7 ∣ ∑ k : Fin 9,
        (digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ)) := by
      apply Finset.dvd_sum
      intro k _
      exact hrepdvd a b hab k
    have heq :
        (∑ k : Fin 9,
          (digits_to_num a + (b k - a k) * (10 : ℤ) ^ (k : ℕ))) =
          digits_to_num a + digits_to_num b + 7 * digits_to_num a := by
      rw [Finset.sum_add_distrib, ← hdiff a b]
      simp
      ring
    rw [heq] at hs
    exact (dvd_sub hs ⟨digits_to_num a, rfl⟩ :
      7 ∣ digits_to_num a + digits_to_num b)
  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have hs := dvd_sub
      (dvd_add (hrepdvd d e h.1 i) (hrepdvd e f h.2 i))
      (hsum d e h.1)
    convert hs using 1 <;> ring
  have hprime : Prime (7 : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by decide)
  rcases hprime.dvd_mul.mp hp with hfd | hpow
  · simpa only [neg_sub] using dvd_neg.mpr hfd
  · exfalso
    have hpow' : (7 : ℕ) ∣ 10 ^ (i : ℕ) := by
      norm_cast at hpow ⊢
    have hten : (7 : ℕ) ∣ 10 :=
      (by decide : Nat.Prime 7).dvd_of_dvd_pow hpow'
    norm_num at hten
