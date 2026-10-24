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
  rcases (hrelation d e).mp h.1 with ⟨_, hde⟩
  rcases (hrelation e f).mp h.2 with ⟨_, hef⟩
  have hde0 := hde (0 : Fin 9)
  have hde1 := hde (1 : Fin 9)
  have hde2 := hde (2 : Fin 9)
  have hde3 := hde (3 : Fin 9)
  have hde4 := hde (4 : Fin 9)
  have hde5 := hde (5 : Fin 9)
  have hde6 := hde (6 : Fin 9)
  have hde7 := hde (7 : Fin 9)
  have hde8 := hde (8 : Fin 9)
  have hef0 := hef (0 : Fin 9)
  have hef1 := hef (1 : Fin 9)
  have hef2 := hef (2 : Fin 9)
  have hef3 := hef (3 : Fin 9)
  have hef4 := hef (4 : Fin 9)
  have hef5 := hef (5 : Fin 9)
  have hef6 := hef (6 : Fin 9)
  have hef7 := hef (7 : Fin 9)
  have hef8 := hef (8 : Fin 9)
  norm_num [hdigits_to_num, Fin.sum_univ_succ] at hde0 hde1 hde2 hde3 hde4 hde5 hde6 hde7 hde8 hef0 hef1 hef2 hef3 hef4 hef5 hef6 hef7 hef8
  fin_cases i <;> norm_num at ⊢ <;> omega
