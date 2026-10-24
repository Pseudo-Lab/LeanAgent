by
  rcases boundedu with ⟨B, T, hBT⟩
  have hr : (Set.range u).Finite := by
    apply (Set.finite_Icc B T).subset
    rintro _ ⟨n, rfl⟩
    exact hBT n
  let v : ℕ → (ℤ × ℤ) × (ℤ × ℤ) :=
    fun n => ((u n, u (n + 1)), (u (n + 2), u (n + 3)))
  have hv : (Set.range v).Finite := by
    apply ((hr.prod hr).prod (hr.prod hr)).subset
    rintro _ ⟨n, rfl⟩
    exact
      ⟨⟨⟨n, rfl⟩, ⟨n + 1, rfl⟩⟩,
       ⟨⟨n + 2, rfl⟩, ⟨n + 3, rfl⟩⟩⟩
  have periodic_of_state :
      ∀ {a b : ℕ}, a < b → v a = v b →
        ∃ c : ℕ, c > 0 ∧ ∀ n ≥ a, u (n + c) = u n := by
    intro a b hab hstate
    have h0 : u a = u b := by
      simpa [v] using
        congrArg (fun x : (ℤ × ℤ) × (ℤ × ℤ) => x.1.1) hstate
    have h1 : u (a + 1) = u (b + 1) := by
      simpa [v] using
        congrArg (fun x : (ℤ × ℤ) × (ℤ × ℤ) => x.1.2) hstate
    have h2 : u (a + 2) = u (b + 2) := by
      simpa [v] using
        congrArg (fun x : (ℤ × ℤ) × (ℤ × ℤ) => x.2.1) hstate
    have h3 : u (a + 3) = u (b + 3) := by
      simpa [v] using
        congrArg (fun x : (ℤ × ℤ) × (ℤ × ℤ) => x.2.2) hstate
    let c : ℕ := b - a
    have hc : c > 0 := by
      dsimp [c]
      omega
    have hac : a + c = b := by
      dsimp [c]
      omega
    refine ⟨c, hc, ?_⟩
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hna
        by_cases hnsmall : n < a + 4
        · have hcases :
              n = a ∨ n = a + 1 ∨ n = a + 2 ∨ n = a + 3 := by
            omega
          rcases hcases with rfl | rfl | rfl | rfl
          · rw [hac]
            exact h0.symm
          · have hi : a + 1 + c = b + 1 := by omega
            rw [hi]
            exact h1.symm
          · have hi : a + 2 + c = b + 2 := by omega
            rw [hi]
            exact h2.symm
          · have hi : a + 3 + c = b + 3 := by omega
            rw [hi]
            exact h3.symm
        · have hu1 : u ((n - 1) + c) = u (n - 1) :=
            ih (n - 1) (by omega) (by omega)
          have hu2 : u ((n - 2) + c) = u (n - 2) :=
            ih (n - 2) (by omega) (by omega)
          have hu3 : u ((n - 3) + c) = u (n - 3) :=
            ih (n - 3) (by omega) (by omega)
          have hu4 : u ((n - 4) + c) = u (n - 4) :=
            ih (n - 4) (by omega) (by omega)
          have hi1 : n + c - 1 = (n - 1) + c := by omega
          have hi2 : n + c - 2 = (n - 2) + c := by omega
          have hi3 : n + c - 3 = (n - 3) + c := by omega
          have hi4 : n + c - 4 = (n - 4) + c := by omega
          have hnc := (hu (n + c) (by omega)).1
          have hn := (hu n (by omega)).1
          rw [hi1, hi2, hi3, hi4, hu1, hu2, hu3, hu4] at hnc
          have hreal : (u (n + c) : ℝ) = u n := hnc.trans hn.symm
          exact_mod_cast hreal
  obtain ⟨a, b, hab, hstate⟩ :=
    hv.exists_ne_map_eq_of_infinite
      (fun n : ℕ => ⟨v n, Set.mem_range_self n⟩)
  have hstate' : v a = v b :=
    congrArg (fun z : Set.range v => z.1) hstate
  rcases lt_or_gt_of_ne hab with hab' | hba
  · obtain ⟨c, hc, hp⟩ := periodic_of_state hab' hstate'
    exact ⟨a, c, hc, hp⟩
  · obtain ⟨c, hc, hp⟩ := periodic_of_state hba hstate'.symm
    exact ⟨b, c, hc, hp⟩