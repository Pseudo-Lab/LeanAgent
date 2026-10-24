by
  classical
  obtain ⟨B, T, hB⟩ := boundedu
  let f : ℕ → (ℤ × ℤ × ℤ × ℤ) :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  have hfinite : Set.Finite (Set.range f) := by
    have hsub : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
      rintro _ ⟨n, rfl⟩
      have h0 := hB n
      have h1 := hB (n + 1)
      have h2 := hB (n + 2)
      have h3 := hB (n + 3)
      simp only [Set.mem_Icc, Prod.le_def, f] at h0 h1 h2 h3 ⊢
      aesop
    have hbox : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      apply Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
      intro x hx
      simp_all [Set.mem_Icc]
    exact hbox.subset hsub
  have hrepeat : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! hne
    have hinj : Function.Injective f := by
      intro i j heq
      by_cases hij : i = j
      · exact hij
      · rcases lt_or_gt_of_ne hij with hij | hij
        · exact (hne i j hij heq).elim
        · exact (hne j i hij heq.symm).elim
    have hinfinite : Set.Infinite (Set.range f) :=
      Set.infinite_range_of_injective hinj
    exact Set.not_infinite.mpr hfinite hinfinite
  obtain ⟨i, j, hij, hf⟩ := hrepeat
  have hstart :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f, Prod.ext_iff] using hf
  have hshift : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      match m with
      | 0 => simpa using hstart.1
      | 1 => simpa using hstart.2.1
      | 2 => simpa using hstart.2.2.1
      | 3 => simpa using hstart.2.2.2
      | m + 4 =>
          have hi := (hu (i + (m + 4)) (by omega)).1
          have hj := (hu (j + (m + 4)) (by omega)).1
          rw [show i + (m + 4) - 1 = i + (m + 3) by omega,
              show i + (m + 4) - 2 = i + (m + 2) by omega,
              show i + (m + 4) - 3 = i + (m + 1) by omega,
              show i + (m + 4) - 4 = i + m by omega] at hi
          rw [show j + (m + 4) - 1 = j + (m + 3) by omega,
              show j + (m + 4) - 2 = j + (m + 2) by omega,
              show j + (m + 4) - 3 = j + (m + 1) by omega,
              show j + (m + 4) - 4 = j + m by omega] at hj
          have e3 : u (i + (m + 3)) = u (j + (m + 3)) :=
            ih (m + 3) (by omega)
          have e2 : u (i + (m + 2)) = u (j + (m + 2)) :=
            ih (m + 2) (by omega)
          have e1 : u (i + (m + 1)) = u (j + (m + 1)) :=
            ih (m + 1) (by omega)
          have e0 : u (i + m) = u (j + m) := ih m (by omega)
          rw [e3, e2, e1, e0] at hi
          have hr := hi.trans hj.symm
          exact_mod_cast hr
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  convert (hshift (n - i)).symm using 1 <;> omega