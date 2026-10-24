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
  have update (x y : Fin 9 → ℤ) (k : Fin 9) :
      digits_to_num (fun j => if j = k then y j else x j) =
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
          (y k - x k) * (10 : ℤ) ^ (k : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp
  have total (x y : Fin 9 → ℤ) :
      digits_to_num y = digits_to_num x +
        ∑ j : Fin 9, (y j - x j) * (10 : ℤ) ^ (j : ℕ) := by
    rw [hdigits_to_num, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hde := ((hrelation d e).mp h.1).2
  have hef := ((hrelation e f).mp h.2).2
  have hde' (j : Fin 9) :
      7 ∣ digits_to_num d + (e j - d j) * (10 : ℤ) ^ (j : ℕ) := by
    rw [← update d e j]
    exact hde j
  have hef' (j : Fin 9) :
      7 ∣ digits_to_num e + (f j - e j) * (10 : ℤ) ^ (j : ℕ) := by
    rw [← update e f j]
    exact hef j
  have hN : 7 ∣ digits_to_num e + digits_to_num d := by
    have hs : 7 ∣ ∑ j : Fin 9,
        (digits_to_num d + (e j - d j) * (10 : ℤ) ^ (j : ℕ)) := by
      apply Finset.dvd_sum
      intro j _
      exact hde' j
    have hz : 7 ∣ 7 * digits_to_num d := ⟨digits_to_num d, rfl⟩
    have hd := dvd_sub hs hz
    rw [total d e]
    convert hd using 1 <;>
      simp [Finset.sum_add_distrib, Finset.sum_const] <;> ring
  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have hc := dvd_add (dvd_sub (hef' i) hN) (hde' i)
    convert hc using 1 <;> ring
  rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp hp with hi | hi
  · simpa only [neg_sub] using dvd_neg.mpr hi
  · exfalso
    have hi' : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by
      norm_cast at hi ⊢
    have hbad : (7 : ℕ) ∣ 10 :=
      Nat.Prime.dvd_of_dvd_pow (by decide) hi'
    norm_num at hbad

#check _root_.putnam_1995_a3
#print axioms _root_.putnam_1995_a3
