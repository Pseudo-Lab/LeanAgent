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
  have hd := ((hrelation d e).mp h.1).2
  have he := ((hrelation e f).mp h.2).2
  have hreplace (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * 10 ^ (i : ℕ) := by
    rw [hdigits_to_num]
    calc
      _ = ∑ j : Fin 9, (a j * 10 ^ (j : ℕ) +
          if j = i then (b j - a j) * 10 ^ (j : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases q : j = i <;> simp [q] <;> ring
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hde (i : Fin 9) :
      7 ∣ digits_to_num d + (e i - d i) * 10 ^ (i : ℕ) := by
    simpa only [hreplace] using hd i
  have hef (i : Fin 9) :
      7 ∣ digits_to_num e + (f i - e i) * 10 ^ (i : ℕ) := by
    simpa only [hreplace] using he i
  have hsum : 7 ∣ digits_to_num e + digits_to_num d := by
    have hs : 7 ∣ ∑ i : Fin 9,
        (digits_to_num d + (e i - d i) * 10 ^ (i : ℕ)) := by
      apply Finset.dvd_sum
      intro i _
      exact hde i
    have hs' : 7 ∣ 9 * digits_to_num d +
        ∑ i : Fin 9, (e i - d i) * 10 ^ (i : ℕ) := by
      simpa [Finset.sum_add_distrib, Finset.sum_const] using hs
    have hseven : 7 ∣ 7 * digits_to_num d := ⟨digits_to_num d, rfl⟩
    convert dvd_sub hs' hseven using 1
    rw [hdigits_to_num]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hprod (i : Fin 9) :
      7 ∣ (f i - d i) * 10 ^ (i : ℕ) := by
    have q := dvd_add (dvd_sub (hef i) hsum) (hde i)
    convert q using 1
    ring
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
