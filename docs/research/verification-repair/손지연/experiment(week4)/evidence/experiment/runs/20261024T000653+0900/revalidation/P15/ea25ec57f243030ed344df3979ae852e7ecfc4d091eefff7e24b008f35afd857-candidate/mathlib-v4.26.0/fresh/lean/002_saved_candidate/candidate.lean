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
  have hs :
      (7 : ℤ) ∣ ∑ k : Fin 9,
        digits_to_num (fun j : Fin 9 => if j = k then e j else d j) := by
    apply Finset.dvd_sum
    intro k hk
    exact hde.2 k
  have h7D : (7 : ℤ) ∣ 7 * digits_to_num d := by
    exact ⟨digits_to_num d, rfl⟩
  have hDEraw := hs.sub h7D
  have hDE : (7 : ℤ) ∣ digits_to_num d + digits_to_num e := by
    convert hDEraw using 1 <;>
      norm_num [hdigits_to_num, Fin.sum_univ_succ] <;>
      ring
  have hi' := ((hde.2 i).add (hef.2 i)).sub hDE
  fin_cases i <;>
    norm_num [hdigits_to_num, Fin.sum_univ_succ] at hi' ⊢ <;>
    omega

#check _root_.putnam_1995_a3
#print axioms _root_.putnam_1995_a3
