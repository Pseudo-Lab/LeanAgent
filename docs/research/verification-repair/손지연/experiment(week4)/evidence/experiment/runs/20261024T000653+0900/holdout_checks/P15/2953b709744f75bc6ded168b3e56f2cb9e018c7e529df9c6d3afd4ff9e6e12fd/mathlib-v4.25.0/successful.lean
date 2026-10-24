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
  intro d e f h i
  have hreplace (x y : Fin 9 → ℤ) (k : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = k then y j else x j) =
        digits_to_num x + (y k - x k) * (10 : ℤ) ^ (k : ℕ) := by
    rw [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = k then y j else x j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9, (x j * (10 : ℤ) ^ (j : ℕ) +
            if j = k then (y j - x j) * (10 : ℤ) ^ (j : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = k <;> simp [hj] <;> ring
      _ = (∑ j : Fin 9, x j * (10 : ℤ) ^ (j : ℕ)) +
          ∑ j : Fin 9, (if j = k then
            (y j - x j) * (10 : ℤ) ^ (j : ℕ) else 0) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin 9, x j * (10 : ℤ) ^ (j : ℕ)) +
          (y k - x k) * (10 : ℤ) ^ (k : ℕ) := by
        simp [Finset.sum_ite_eq']
  have hdiff (x y : Fin 9 → ℤ) :
      (∑ k : Fin 9, (y k - x k) * (10 : ℤ) ^ (k : ℕ)) =
        digits_to_num y - digits_to_num x := by
    rw [hdigits_to_num, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsum (x y : Fin 9 → ℤ)
      (hy : ∀ k : Fin 9,
        7 ∣ digits_to_num (fun j : Fin 9 => if j = k then y j else x j)) :
      7 ∣ digits_to_num x + digits_to_num y := by
    have hs : 7 ∣ ∑ k : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = k then y j else x j) := by
      apply Finset.dvd_sum
      intro k _
      exact hy k
    have heq :
        (∑ k : Fin 9,
          digits_to_num (fun j : Fin 9 => if j = k then y j else x j)) =
          8 * digits_to_num x + digits_to_num y := by
      calc
        _ = ∑ k : Fin 9, (digits_to_num x +
            (y k - x k) * (10 : ℤ) ^ (k : ℕ)) := by
          apply Finset.sum_congr rfl
          intro k _
          exact hreplace x y k
        _ = 8 * digits_to_num x + digits_to_num y := by
          rw [Finset.sum_add_distrib, hdiff]
          simp [Finset.sum_const, Finset.card_fin] <;> ring
    rw [heq] at hs
    have hseven : 7 ∣ 7 * digits_to_num x := ⟨digits_to_num x, by ring⟩
    have ht := dvd_sub hs hseven
    convert ht using 1 <;> ring
  have hde := (hrelation d e).mp h.1
  have hef := (hrelation e f).mp h.2
  have hs : 7 ∣ digits_to_num d + digits_to_num e :=
    hsum d e hde.2
  have ha :
      7 ∣ digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [← hreplace d e i]
    exact hde.2 i
  have hb :
      7 ∣ digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [← hreplace e f i]
    exact hef.2 i
  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have ht := dvd_add (dvd_sub hb hs) ha
    convert ht using 1 <;> ring
  have hfd : (7 : ℤ) ∣ f i - d i := by
    have hprime : Prime (7 : ℤ) :=
      Int.prime_iff_natAbs_prime.mpr (by decide)
    rcases hprime.dvd_mul.mp hp with hfd | hpow
    · exact hfd
    · fin_cases i <;> norm_num at hpow
  have hneg : (7 : ℤ) ∣ -(f i - d i) := dvd_neg.mpr hfd
  convert hneg using 1 <;> ring
