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
  have replace_num (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    simp only [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ (j : ℕ)) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
            if j = i then (b i - a i) * (10 : ℤ) ^ (i : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : j = i
        · subst j
          simp
          ring
        · simp [hij]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := rfl
  have num_diff (a b : Fin 9 → ℤ) :
      digits_to_num b = digits_to_num a +
        ∑ i : Fin 9, (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    simp only [hdigits_to_num]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hde : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j : Fin 9 => if j = i then e j else d j) :=
    ((hrelation d e).mp h.1).2
  have hef : ∀ i : Fin 9,
      7 ∣ digits_to_num (fun j : Fin 9 => if j = i then f j else e j) :=
    ((hrelation e f).mp h.2).2
  have hab : ∀ i : Fin 9,
      7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := by
    intro i
    have hi := hde i
    rw [replace_num d e i] at hi
    convert hi using 1 <;> ring
  have hbc : ∀ i : Fin 9,
      7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e := by
    intro i
    have hi := hef i
    rw [replace_num e f i] at hi
    convert hi using 1 <;> ring
  have hsum :
      7 ∣ ∑ i : Fin 9,
        ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) := by
    apply Finset.dvd_sum
    intro i _
    exact hab i
  have heq :
      (∑ i : Fin 9,
        ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d)) -
          7 * digits_to_num d = digits_to_num e + digits_to_num d := by
    rw [Finset.sum_add_distrib, num_diff d e]
    simp [Finset.card_fin]
    ring
  have hglob : 7 ∣ digits_to_num e + digits_to_num d := by
    rw [← heq]
    exact dvd_sub hsum ⟨digits_to_num d, rfl⟩
  intro i
  have hpow : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have ht := dvd_add (dvd_sub (hbc i) hglob) (hab i)
    convert ht using 1 <;> ring
  rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp hpow with hi | hi
  · simpa only [neg_sub] using (dvd_neg.mpr hi)
  · exfalso
    have hpw : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by
      norm_cast at hi ⊢
      simpa [Int.coe_nat_dvd_left] using hi
    have hten : (7 : ℕ) ∣ 10 :=
      Nat.Prime.dvd_of_dvd_pow (by decide) hpw
    norm_num at hten

#check _root_.putnam_1995_a3
#print axioms _root_.putnam_1995_a3
