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
  rintro d e f ⟨hde_rel, hef_rel⟩ i
  have hde := (hrelation d e).mp hde_rel
  have hef := (hrelation e f).mp hef_rel
  have hd0 := hde.2 (0 : Fin 9)
  have hd1 := hde.2 (1 : Fin 9)
  have hd2 := hde.2 (2 : Fin 9)
  have hd3 := hde.2 (3 : Fin 9)
  have hd4 := hde.2 (4 : Fin 9)
  have hd5 := hde.2 (5 : Fin 9)
  have hd6 := hde.2 (6 : Fin 9)
  have hd7 := hde.2 (7 : Fin 9)
  have hd8 := hde.2 (8 : Fin 9)
  have he0 := hef.2 (0 : Fin 9)
  have he1 := hef.2 (1 : Fin 9)
  have he2 := hef.2 (2 : Fin 9)
  have he3 := hef.2 (3 : Fin 9)
  have he4 := hef.2 (4 : Fin 9)
  have he5 := hef.2 (5 : Fin 9)
  have he6 := hef.2 (6 : Fin 9)
  have he7 := hef.2 (7 : Fin 9)
  have he8 := hef.2 (8 : Fin 9)
  norm_num [hdigits_to_num, Fin.sum_univ_succ] at hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 he0 he1 he2 he3 he4 he5 he6 he7 he8
  rcases hd0 with ⟨kd0, hd0⟩
  rcases hd1 with ⟨kd1, hd1⟩
  rcases hd2 with ⟨kd2, hd2⟩
  rcases hd3 with ⟨kd3, hd3⟩
  rcases hd4 with ⟨kd4, hd4⟩
  rcases hd5 with ⟨kd5, hd5⟩
  rcases hd6 with ⟨kd6, hd6⟩
  rcases hd7 with ⟨kd7, hd7⟩
  rcases hd8 with ⟨kd8, hd8⟩
  rcases he0 with ⟨ke0, he0⟩
  rcases he1 with ⟨ke1, he1⟩
  rcases he2 with ⟨ke2, he2⟩
  rcases he3 with ⟨ke3, he3⟩
  rcases he4 with ⟨ke4, he4⟩
  rcases he5 with ⟨ke5, he5⟩
  rcases he6 with ⟨ke6, he6⟩
  rcases he7 with ⟨ke7, he7⟩
  rcases he8 with ⟨ke8, he8⟩
  fin_cases i
  · change ∃ k : ℤ, d 0 - f 0 = 7 * k
    omega
  · change ∃ k : ℤ, d 1 - f 1 = 7 * k
    omega
  · change ∃ k : ℤ, d 2 - f 2 = 7 * k
    omega
  · change ∃ k : ℤ, d 3 - f 3 = 7 * k
    omega
  · change ∃ k : ℤ, d 4 - f 4 = 7 * k
    omega
  · change ∃ k : ℤ, d 5 - f 5 = 7 * k
    omega
  · change ∃ k : ℤ, d 6 - f 6 = 7 * k
    omega
  · change ∃ k : ℤ, d 7 - f 7 = 7 * k
    omega
  · change ∃ k : ℤ, d 8 - f 8 = 7 * k
    omega
