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
  have hchange (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * 10 ^ (i : ℕ) := by
    rw [hdigits_to_num]
    calc
      ∑ j : Fin 9, (if j = i then b j else a j) * 10 ^ (j : ℕ) =
          ∑ j : Fin 9, (a j * 10 ^ (j : ℕ) +
            if j = i then (b j - a j) * 10 ^ (j : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i
        · simp [hj]
          ring
        · simp [hj]
      _ = (∑ j : Fin 9, a j * 10 ^ (j : ℕ)) +
          (b i - a i) * 10 ^ (i : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp
  have htotal (a b : Fin 9 → ℤ) :
      digits_to_num b - digits_to_num a =
        ∑ i : Fin 9, (b i - a i) * 10 ^ (i : ℕ) := by
    rw [hdigits_to_num, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpair : ∀ {a b : Fin 9 → ℤ}, relation a b →
      7 ∣ digits_to_num a + digits_to_num b := by
    intro a b hab
    have hr := ((hrelation a b).mp hab).2
    have hs : 7 ∣ ∑ i : Fin 9,
        digits_to_num (fun j => if j = i then b j else a j) := by
      apply Finset.dvd_sum
      intro i _
      exact hr i
    have hsum :
        (∑ i : Fin 9, digits_to_num (fun j => if j = i then b j else a j)) =
          (digits_to_num a + digits_to_num b) + 7 * digits_to_num a := by
      calc
        _ = ∑ i : Fin 9, (digits_to_num a +
              (b i - a i) * 10 ^ (i : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hchange a b i
        _ = 9 * digits_to_num a +
              ∑ i : Fin 9, (b i - a i) * 10 ^ (i : ℕ) := by
          rw [Finset.sum_add_distrib]
          simp
          <;> ring
        _ = (digits_to_num a + digits_to_num b) +
              7 * digits_to_num a := by
          rw [← htotal a b]
          ring
    rw [hsum] at hs
    have hseven : 7 ∣ 7 * digits_to_num a := ⟨digits_to_num a, by ring⟩
    have h := dvd_sub hs hseven
    convert h using 1 <;> ring
  intro d e f h
  rcases h with ⟨hde, hef⟩
  have rde := ((hrelation d e).mp hde).2
  have ref := ((hrelation e f).mp hef).2
  intro i
  have hp : 7 ∣ (f i - d i) * 10 ^ (i : ℕ) := by
    have hs := dvd_add (rde i) (ref i)
    rw [hchange d e i, hchange e f i] at hs
    have ht := dvd_sub hs (hpair hde)
    convert ht using 1 <;> ring
  have hfd : 7 ∣ f i - d i := by
    have hprime : Int.Prime 7 :=
      Int.prime_iff_natAbs_prime.mpr (by decide)
    rcases hprime.dvd_mul.mp hp with hp | hp
    · exact hp
    · exfalso
      have hnat : (7 : ℕ) ∣ 10 ^ (i : ℕ) := by
        norm_cast at hp ⊢
        <;> simpa [Int.coe_nat_dvd_left] using hp
      have hbad : (7 : ℕ) ∣ 10 :=
        Nat.Prime.dvd_of_dvd_pow (by decide) hnat
      norm_num at hbad
  convert dvd_neg.mpr hfd using 1 <;> ring
