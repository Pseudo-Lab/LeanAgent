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
  have hrepl (a b : Fin 9 → ℤ) (i : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ i.1 := by
    rw [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ j.1) =
          ∑ j : Fin 9, (a j * (10 : ℤ) ^ j.1 +
            if j = i then (b i - a i) * (10 : ℤ) ^ i.1 else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i
            · subst j
              simp
              ring
            · simp [hji]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ j.1) +
          (b i - a i) * (10 : ℤ) ^ i.1 := by
            rw [Finset.sum_add_distrib]
            simp
  intro d e f hrel
  rcases (hrelation d e).mp hrel.1 with ⟨hboundde, hdivde⟩
  rcases (hrelation e f).mp hrel.2 with ⟨hboundef, hdivef⟩
  have hde : ∀ i : Fin 9,
      7 ∣ digits_to_num d + (e i - d i) * (10 : ℤ) ^ i.1 := by
    intro i
    rw [← hrepl d e i]
    exact hdivde i
  have hef : ∀ i : Fin 9,
      7 ∣ digits_to_num e + (f i - e i) * (10 : ℤ) ^ i.1 := by
    intro i
    rw [← hrepl e f i]
    exact hdivef i
  have hsum :
      7 ∣ ∑ i : Fin 9,
        (digits_to_num d + (e i - d i) * (10 : ℤ) ^ i.1) := by
    apply Finset.dvd_sum
    intro i hi
    exact hde i
  have hsum_id :
      (∑ i : Fin 9,
          (digits_to_num d + (e i - d i) * (10 : ℤ) ^ i.1)) -
          7 * digits_to_num d =
        digits_to_num d + digits_to_num e := by
    simp only [hdigits_to_num]
    simp_rw [sub_mul]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp
    ring
  have hde_sum : 7 ∣ digits_to_num d + digits_to_num e := by
    rw [← hsum_id]
    exact dvd_sub hsum ⟨digits_to_num d, rfl⟩
  intro i
  have hboth :
      7 ∣ (digits_to_num d + (e i - d i) * (10 : ℤ) ^ i.1) +
        (digits_to_num e + (f i - e i) * (10 : ℤ) ^ i.1) :=
    dvd_add (hde i) (hef i)
  have hprod : 7 ∣ (f i - d i) * (10 : ℤ) ^ i.1 := by
    have hid :
        ((digits_to_num d + (e i - d i) * (10 : ℤ) ^ i.1) +
            (digits_to_num e + (f i - e i) * (10 : ℤ) ^ i.1)) -
            (digits_to_num d + digits_to_num e) =
          (f i - d i) * (10 : ℤ) ^ i.1 := by
      ring
    rw [← hid]
    exact dvd_sub hboth hde_sum
  have hc0 : IsCoprime (7 : ℤ) (10 : ℤ) := by
    norm_num
  have hc : IsCoprime (7 : ℤ) ((10 : ℤ) ^ i.1) := hc0.pow_right
  have hx : 7 ∣ f i - d i := hc.dvd_of_dvd_mul_right hprod
  rcases hx with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  linear_combination -hk

#check _root_.putnam_1995_a3
#print axioms _root_.putnam_1995_a3
