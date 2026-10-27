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
  intro d e f h
  rcases h with ⟨hde, hef⟩
  have hde' := ((hrelation d e).mp hde).2
  have hef' := ((hrelation e f).mp hef).2
  have hchange (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    classical
    calc
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
          ∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ (j : ℕ) := by
            simp [hdigits_to_num]
      _ = ∑ j : Fin 9, (a j * (10 : ℤ) ^ (j : ℕ) +
          if j = i then (b i - a i) * (10 : ℤ) ^ (i : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hji : j = i
            · subst j
              simp <;> ring
            · simp [hji]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
            rw [Finset.sum_add_distrib]
            simp [Finset.sum_ite_eq', Finset.mem_univ]
      _ = digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
            simp [hdigits_to_num]
  have hdiff (a b : Fin 9 → ℤ) :
      (∑ i : Fin 9, (b i - a i) * (10 : ℤ) ^ (i : ℕ)) =
        digits_to_num b - digits_to_num a := by
    calc
      (∑ i : Fin 9, (b i - a i) * (10 : ℤ) ^ (i : ℕ)) =
          ∑ i : Fin 9, (b i * (10 : ℤ) ^ (i : ℕ) -
            a i * (10 : ℤ) ^ (i : ℕ)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin 9, b i * (10 : ℤ) ^ (i : ℕ)) -
          ∑ i : Fin 9, a i * (10 : ℤ) ^ (i : ℕ) := by
            rw [Finset.sum_sub_distrib]
      _ = digits_to_num b - digits_to_num a := by
            simp [hdigits_to_num]
  have hsum : 7 ∣ ∑ i : Fin 9,
      (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ)) := by
    apply Finset.dvd_sum
    intro i _
    rw [← hchange d e i]
    exact hde' i
  have heq : (∑ i : Fin 9,
      (digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ))) =
      8 * digits_to_num d + digits_to_num e := by
    rw [Finset.sum_add_distrib, hdiff d e]
    simp <;> ring
  rw [heq] at hsum
  have hseven : 7 ∣ 7 * digits_to_num d := ⟨digits_to_num d, by ring⟩
  have hnum : 7 ∣ digits_to_num d + digits_to_num e := by
    have ht := dvd_sub hsum hseven
    convert ht using 1 <;> ring
  intro i
  have ha : 7 ∣ digits_to_num d +
      (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [← hchange d e i]
    exact hde' i
  have hb : 7 ∣ digits_to_num e +
      (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
    rw [← hchange e f i]
    exact hef' i
  have hp : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have ht := dvd_sub (dvd_add ha hb) hnum
    convert ht using 1 <;> ring
  rcases (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp hp with hfd | hpow
  · simpa only [neg_sub] using dvd_neg.mpr hfd
  · exfalso
    have hpow' : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by
      norm_cast at hpow ⊢
      simpa [Int.coe_nat_dvd_left] using hpow
    have hten : (7 : ℕ) ∣ 10 :=
      Nat.Prime.dvd_of_dvd_pow (by decide) hpow'
    norm_num at hten
