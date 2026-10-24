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
  have hchange : ∀ (a b : Fin 9 → ℤ) (i : Fin 9),
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
        digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
    intro a b i
    calc
      digits_to_num (fun j : Fin 9 => if j = i then b j else a j) =
          ∑ j : Fin 9, (if j = i then b j else a j) * (10 : ℤ) ^ (j : ℕ) := by
        simp [hdigits_to_num]
      _ = ∑ j : Fin 9,
          (a j * (10 : ℤ) ^ (j : ℕ) +
            (if j = i then b j - a j else 0) * (10 : ℤ) ^ (j : ℕ)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i
        · simp [hj]
          ring
        · simp [hj]
      _ = (∑ j : Fin 9, a j * (10 : ℤ) ^ (j : ℕ)) +
          (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq', Finset.mem_univ]
      _ = digits_to_num a + (b i - a i) * (10 : ℤ) ^ (i : ℕ) := by
        simp [hdigits_to_num]
  have ha : ∀ i : Fin 9,
      7 ∣ (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d := by
    intro i
    have hi := hde i
    rw [hchange d e i] at hi
    have heq :
        (e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d =
          digits_to_num d + (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
      ring
    rw [heq]
    exact hi
  have hb : ∀ i : Fin 9,
      7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e := by
    intro i
    have hi := hef i
    rw [hchange e f i] at hi
    have heq :
        (f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e =
          digits_to_num e + (f i - e i) * (10 : ℤ) ^ (i : ℕ) := by
      ring
    rw [heq]
    exact hi
  have hdiff :
      digits_to_num e = digits_to_num d +
        ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    calc
      digits_to_num e = ∑ i : Fin 9, e i * (10 : ℤ) ^ (i : ℕ) := by
        simp [hdigits_to_num]
      _ = ∑ i : Fin 9, (d i + (e i - d i)) * (10 : ℤ) ^ (i : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i : Fin 9,
          (d i * (10 : ℤ) ^ (i : ℕ) +
            (e i - d i) * (10 : ℤ) ^ (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i : Fin 9, d i * (10 : ℤ) ^ (i : ℕ)) +
          ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
        rw [Finset.sum_add_distrib]
      _ = digits_to_num d +
          ∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ) := by
        simp [hdigits_to_num]
  have hraw :
      7 ∣ ∑ i : Fin 9,
        ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) := by
    apply Finset.dvd_sum
    intro i _
    exact ha i
  have hraw_eq :
      (∑ i : Fin 9,
        ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d)) =
        (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) +
          9 * digits_to_num d := by
    calc
      (∑ i : Fin 9,
        ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d)) =
          (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) +
            ∑ i : Fin 9, digits_to_num d := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin 9, (e i - d i) * (10 : ℤ) ^ (i : ℕ)) +
          9 * digits_to_num d := by
        simp [Finset.sum_const]
  have hraw_eq' :
      (∑ i : Fin 9,
        ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d)) =
        digits_to_num e + 8 * digits_to_num d := by
    linarith [hraw_eq, hdiff]
  rw [hraw_eq'] at hraw
  have hseven : 7 ∣ 7 * digits_to_num d := by
    use digits_to_num d
  have hsum : 7 ∣ digits_to_num e + digits_to_num d := by
    have hs := dvd_sub hraw hseven
    have heq :
        (digits_to_num e + 8 * digits_to_num d) - 7 * digits_to_num d =
          digits_to_num e + digits_to_num d := by
      ring
    rw [heq] at hs
    exact hs
  intro i
  have hprod : 7 ∣ (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
    have h₁ :
        7 ∣ (f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d := by
      have hs := dvd_sub (hb i) hsum
      have heq :
          ((f i - e i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num e) -
              (digits_to_num e + digits_to_num d) =
            (f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d := by
        ring
      rw [heq] at hs
      exact hs
    have hs := dvd_add h₁ (ha i)
    have heq :
        ((f i - e i) * (10 : ℤ) ^ (i : ℕ) - digits_to_num d) +
            ((e i - d i) * (10 : ℤ) ^ (i : ℕ) + digits_to_num d) =
          (f i - d i) * (10 : ℤ) ^ (i : ℕ) := by
      ring
    rw [heq] at hs
    exact hs
  have hnot : ¬(7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by
    intro hp
    have hnat : (7 : ℕ) ∣ (10 : ℕ) ^ (i : ℕ) := by
      norm_cast at hp ⊢
    have hten : (7 : ℕ) ∣ 10 := by
      exact Nat.Prime.dvd_of_dvd_pow (by decide) hnat
    norm_num at hten
  have hor :
      (7 : ℤ) ∣ (f i - d i) ∨ (7 : ℤ) ∣ (10 : ℤ) ^ (i : ℕ) := by
    apply (Int.prime_iff_natAbs_prime.mpr (by decide)).dvd_mul.mp
    exact hprod
  cases hor with
  | inl hfd =>
      have hn : (7 : ℤ) ∣ -(f i - d i) := dvd_neg.mpr hfd
      simpa only [neg_sub] using hn
  | inr hp =>
      exact (hnot hp).elim
