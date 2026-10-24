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
  intro d e f h
  have hde : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j : Fin 9 => if j = i then e j else d j) :=
    ((hrelation d e).mp h.1).2
  have hef : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j : Fin 9 => if j = i then f j else e j) :=
    ((hrelation e f).mp h.2).2
  have hchange (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    simp only [hdigits_to_num]
    calc
      ∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ (j : ℕ) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
            if j = i then (b i - a i) * (10 : ℤ) ^ (i : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j
          simp <;> ring
        · simp [hj]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp
  have hdiff (a b : Fin 9 → ℤ) :
      digits_to_num b - digits_to_num a =
        ∑ i : Fin 9, (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    simp only [hdigits_to_num]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hd (i : Fin 9) :
      7 ∣ digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [← hchange d e i]
    exact hde i
  have he (i : Fin 9) :
      7 ∣ digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [← hchange e f i]
    exact hef i
  have hsum :
      7 ∣ ∑ i : Fin 9,
        (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ)) := by
    apply Finset.dvd_sum
    intro i _
    exact hd i
  have hsum_eq :
      (∑ i : Fin 9,
        (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ))) =
          (digits_to_num d + digits_to_num e) + 7 * digits_to_num d := by
    rw [Finset.sum_add_distrib, ← hdiff d e]
    simp <;> ring
  have hnum : 7 ∣ digits_to_num d + digits_to_num e := by
    rw [hsum_eq] at hsum
    have hseven : (7 : ℤ) ∣ 7 * digits_to_num d :=
      ⟨digits_to_num d, rfl⟩
    simpa only [add_sub_cancel_right] using dvd_sub hsum hseven
  intro i
  have hcombined :
      7 ∣ (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) +
          (digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ))) -
        (digits_to_num d + digits_to_num e) :=
    dvd_sub (dvd_add (hd i) (he i)) hnum
  have hprod : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    convert hcombined using 1 <;> ring
  have hfd : (7 : ℤ) ∣ f i - d i := by
    rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp hprod with hfd | hp
    · exact hfd
    · have hp' : (7 : ℕ) ∣ 10 ^ (i : ℕ) := by
        exact_mod_cast hp
      have hbad : (7 : ℕ) ∣ 10 :=
        (show Nat.Prime 7 by decide).dvd_of_dvd_pow hp'
      norm_num at hbad
  have hneg : (7 : ℤ) ∣ -(f i - d i) := dvd_neg.mpr hfd
  simpa using hneg

#check _root_.putnam_1995_a3
#print axioms _root_.putnam_1995_a3
