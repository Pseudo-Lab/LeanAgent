by
  rcases boundedu with ⟨B, T, hBT⟩
  let S := Finset.Icc B T
  let v : ℕ → {x : ℤ // x ∈ S} := fun k =>
    ⟨u k, by simpa [S] using hBT k⟩
  let f : ℕ → (Fin 4 → {x : ℤ // x ∈ S}) := fun k i => v (k + i)
  obtain ⟨p, q, hpq, hpqf⟩ := Finite.exists_ne_map_eq_of_infinite f
  obtain ⟨a, b, hab, habf⟩ : ∃ a b : ℕ, a < b ∧ f a = f b := by
    rcases lt_or_gt_of_ne hpq with hpqlt | hpqgt
    · exact ⟨p, q, hpqlt, hpqf⟩
    · exact ⟨q, p, hpqgt, hpqf.symm⟩
  have hinit (i : Fin 4) : u (a + (i : ℕ)) = u (b + (i : ℕ)) := by
    simpa [f, v] using congrArg Subtype.val (congrFun habf i)
  let c := b - a
  have hc : 0 < c := by
    dsimp [c]
    omega
  have hbc : b = a + c := by
    dsimp [c]
    omega
  have hperiod : ∀ k : ℕ, a ≤ k → u (k + c) = u k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        by_cases hsmall : k < a + 4
        · let i : Fin 4 := ⟨k - a, by omega⟩
          have hi := hinit i
          have haidx : a + (i : ℕ) = k := by
            dsimp [i]
            omega
          have hbidx : b + (i : ℕ) = k + c := by
            dsimp [i]
            omega
          rw [haidx, hbidx] at hi
          exact hi.symm
        · have hk4 : 4 ≤ k := by omega
          have hkc4 : 4 ≤ k + c := by omega
          have h1 : u ((k - 1) + c) = u (k - 1) := ih (k - 1) (by omega) (by omega)
          have h2 : u ((k - 2) + c) = u (k - 2) := ih (k - 2) (by omega) (by omega)
          have h3 : u ((k - 3) + c) = u (k - 3) := ih (k - 3) (by omega) (by omega)
          have h4 : u ((k - 4) + c) = u (k - 4) := ih (k - 4) (by omega) (by omega)
          have hidx1 : (k + c) - 1 = (k - 1) + c := by omega
          have hidx2 : (k + c) - 2 = (k - 2) + c := by omega
          have hidx3 : (k + c) - 3 = (k - 3) + c := by omega
          have hidx4 : (k + c) - 4 = (k - 4) + c := by omega
          have ek := (hu k hk4).1
          have ekc := (hu (k + c) hkc4).1
          have ekc' :
              (u (k + c) : ℝ) =
                ((u (k - 1) + u (k - 2) + u (k - 3) * u (k - 4)) : ℝ) /
                  (u (k - 1) * u (k - 2) + u (k - 3) + u (k - 4)) := by
            rw [ekc]
            rw [hidx1, hidx2, hidx3, hidx4, h1, h2, h3, h4]
          exact_mod_cast ekc'.trans ek.symm
  exact ⟨a, c, hc, hperiod⟩