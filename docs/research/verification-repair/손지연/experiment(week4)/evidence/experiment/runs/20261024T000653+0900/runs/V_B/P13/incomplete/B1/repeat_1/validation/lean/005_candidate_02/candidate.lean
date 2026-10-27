import Mathlib
import Aesop

set_option maxHeartbeats 0

open Set Function


theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  classical
  rcases boundedu with ⟨B, T, hbounds⟩
  let S : Set ℤ := Set.Icc B T
  letI : Fintype S := (Set.finite_Icc B T).fintype
  let f : ℕ → (Fin 4 → S) := fun n i =>
    ⟨u (n + i), hbounds (n + i)⟩
  obtain ⟨a, b, hab, hfab⟩ :=
    Finite.exists_ne_map_eq_of_infinite f
  have hpq : ∃ p q : ℕ, p < q ∧ f p = f q := by
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact ⟨a, b, hlt, hfab⟩
    · exact ⟨b, a, hgt, hfab.symm⟩
  rcases hpq with ⟨p, q, hpq, hstate⟩
  let c := q - p
  have hc : p + c = q := by
    dsimp [c]
    omega
  have hcpos : 0 < c := by
    dsimp [c]
    omega
  have hbase : ∀ i : Fin 4, u (p + (i : ℕ)) = u (q + (i : ℕ)) := by
    intro i
    simpa [f] using
      congrArg (fun g : Fin 4 → S => (g i : ℤ)) hstate
  have hperiod : ∀ k : ℕ, u (p + k + c) = u (p + k) := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih
    by_cases hk : k < 4
    · have h := hbase ⟨k, hk⟩
      convert h.symm using 1 <;> omega
    · have hk4 : 4 ≤ k := by omega
      have h1 := ih (k - 1) (by omega)
      have h2 := ih (k - 2) (by omega)
      have h3 := ih (k - 3) (by omega)
      have h4 := ih (k - 4) (by omega)
      have e1 : u ((p + k + c) - 1) = u ((p + k) - 1) := by
        convert h1 using 1 <;> omega
      have e2 : u ((p + k + c) - 2) = u ((p + k) - 2) := by
        convert h2 using 1 <;> omega
      have e3 : u ((p + k + c) - 3) = u ((p + k) - 3) := by
        convert h3 using 1 <;> omega
      have e4 : u ((p + k + c) - 4) = u ((p + k) - 4) := by
        convert h4 using 1 <;> omega
      have hleft := (hu (p + k + c) (by omega)).1
      have hright := (hu (p + k) (by omega)).1
      rw [e1, e2, e3, e4] at hleft
      have hcast : (u (p + k + c) : ℝ) = (u (p + k) : ℝ) :=
        hleft.trans hright.symm
      exact_mod_cast hcast
  refine ⟨p, c, hcpos, ?_⟩
  intro n hn
  have h := hperiod (n - p)
  have hnp : p + (n - p) = n := by omega
  rw [hnp] at h
  exact h

#check _root_.putnam_1964_a4
#print axioms _root_.putnam_1964_a4
