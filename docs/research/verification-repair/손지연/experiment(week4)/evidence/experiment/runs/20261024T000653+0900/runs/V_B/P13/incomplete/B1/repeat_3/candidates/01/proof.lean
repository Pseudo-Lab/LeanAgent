by
  classical
  rcases boundedu with ⟨B, T, hBT⟩
  let v : ℕ → {z : ℤ // z ∈ Finset.Icc B T} := fun n =>
    ⟨u n, by
      rw [Finset.mem_Icc]
      exact hBT n⟩
  let state := fun n : ℕ =>
    (v n, v (n + 1), v (n + 2), v (n + 3))
  obtain ⟨i, j, hij, hijstate⟩ :=
    Finite.exists_ne_map_eq_of_infinite state
  obtain ⟨a, b, hab, hstate⟩ :
      ∃ a b : ℕ, a < b ∧ state a = state b := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, hlt, hijstate⟩
    · exact ⟨j, i, hgt, hijstate.symm⟩
  have habvals :
      u a = u b ∧
        u (a + 1) = u (b + 1) ∧
        u (a + 2) = u (b + 2) ∧
        u (a + 3) = u (b + 3) := by
    simpa [state, v] using hstate
  rcases habvals with ⟨h0, h1, h2, h3⟩
  have hper : ∀ k : ℕ, u (b + k) = u (a + k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk0 : k = 0
      · subst k
        simpa using h0.symm
      by_cases hk1 : k = 1
      · subst k
        simpa using h1.symm
      by_cases hk2 : k = 2
      · subst k
        simpa using h2.symm
      by_cases hk3 : k = 3
      · subst k
        simpa using h3.symm
      have hk4 : 4 ≤ k := by omega
      have hp1 : u (b + k - 1) = u (a + k - 1) := by
        rw [show b + k - 1 = b + (k - 1) by omega,
          show a + k - 1 = a + (k - 1) by omega]
        exact ih (k - 1) (by omega)
      have hp2 : u (b + k - 2) = u (a + k - 2) := by
        rw [show b + k - 2 = b + (k - 2) by omega,
          show a + k - 2 = a + (k - 2) by omega]
        exact ih (k - 2) (by omega)
      have hp3 : u (b + k - 3) = u (a + k - 3) := by
        rw [show b + k - 3 = b + (k - 3) by omega,
          show a + k - 3 = a + (k - 3) by omega]
        exact ih (k - 3) (by omega)
      have hp4 : u (b + k - 4) = u (a + k - 4) := by
        rw [show b + k - 4 = b + (k - 4) by omega,
          show a + k - 4 = a + (k - 4) by omega]
        exact ih (k - 4) (by omega)
      have hb := (hu (b + k) (by omega)).1
      have ha := (hu (a + k) (by omega)).1
      rw [hp1, hp2, hp3, hp4] at hb
      have hreal : (u (b + k) : ℝ) = (u (a + k) : ℝ) :=
        hb.trans ha.symm
      exact_mod_cast hreal
  refine ⟨a, b - a, by omega, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have heq : a + k + (b - a) = b + k := by omega
  rw [heq]
  exact hper k