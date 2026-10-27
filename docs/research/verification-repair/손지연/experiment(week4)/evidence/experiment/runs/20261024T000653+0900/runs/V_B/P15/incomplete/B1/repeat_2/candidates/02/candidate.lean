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
  have hde := (hrelation d e).mp h.1
  have hef := (hrelation e f).mp h.2
  have hrepl (a b : Fin 9 → ℤ) (k : Fin 9) :
      digits_to_num (fun j : Fin 9 => if j = k then b j else a j) =
        digits_to_num a + (b k - a k) * 10 ^ k.1 := by
    simp only [hdigits_to_num]
    calc
      (∑ j : Fin 9, (if j = k then b j else a j) * 10 ^ j.1) =
          ∑ j : Fin 9, (a j * 10 ^ j.1 +
            if j = k then (b j - a j) * 10 ^ j.1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjk : j = k
        · subst j
          simp
          ring
        · simp [hjk]
      _ = (∑ j : Fin 9, a j * 10 ^ j.1) +
          (b k - a k) * 10 ^ k.1 := by
        rw [Finset.sum_add_distrib]
        simp
  have hs :
      (7 : ℤ) ∣ ∑ k : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = k then e j else d j) := by
    apply Finset.dvd_sum
    intro k hk
    exact hde.2 k
  have hsumid :
      (∑ k : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = k then e j else d j)) =
        8 * digits_to_num d + digits_to_num e := by
    calc
      (∑ k : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = k then e j else d j)) =
          ∑ k : Fin 9,
            (digits_to_num d + (e k - d k) * 10 ^ k.1) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hrepl d e k
      _ = 8 * digits_to_num d + digits_to_num e := by
        norm_num [hdigits_to_num, Fin.sum_univ_succ] <;> ring
  rw [hsumid] at hs
  have h7D : (7 : ℤ) ∣ 7 * digits_to_num d := by
    exact ⟨digits_to_num d, rfl⟩
  have hDEraw := hs.sub h7D
  have hDE : (7 : ℤ) ∣ digits_to_num d + digits_to_num e := by
    convert hDEraw using 1 <;> ring
  have hp := ((hde.2 i).add (hef.2 i)).sub hDE
  rw [hrepl d e i, hrepl e f i] at hp
  have hp' : (7 : ℤ) ∣ (f i - d i) * 10 ^ i.1 := by
    convert hp using 1 <;> ring
  fin_cases i <;>
    norm_num at hp' ⊢ <;>
    rcases hp' with ⟨q, hq⟩ <;>
    omega
