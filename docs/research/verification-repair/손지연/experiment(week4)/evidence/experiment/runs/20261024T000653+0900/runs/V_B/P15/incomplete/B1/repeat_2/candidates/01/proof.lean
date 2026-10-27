by
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