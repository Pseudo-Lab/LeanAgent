by
  classical
  obtain ⟨B, T, hB⟩ := boundedu
  let f : ℕ → (ℤ × ℤ × ℤ × ℤ) :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  have hfin : Set.Finite (Set.range f) := by
    have hsub : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
      rintro _ ⟨n, rfl⟩
      have h0 := hB n
      have h1 := hB (n + 1)
      have h2 := hB (n + 2)
      have h3 := hB (n + 3)
      simp only [Set.mem_Icc, Prod.le_def]
      aesop
    have hbox : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      apply Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
      intro x hx
      simpa [Set.mem_Icc] using hx
    exact hbox.subset hsub
  have hpigeon : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! h
    have hinj : Function.Injective f := by
      intro a b hab
      rcases lt_trichotomy a b with hablt | rfl | hbalt
      · exact (h a b hablt hab).elim
      · rfl
      · exact (h b a hbalt hab.symm).elim
    have hinf : Set.Infinite (Set.range f) :=
      Set.infinite_range_of_injective hinj
    exact Set.not_infinite.mpr hfin hinf
  obtain ⟨i, j, hij, hf⟩ := hpigeon
  have heq :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa only [f, Prod.mk.injEq] using hf
  have hshift : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        match m with
        | 0 => simpa using heq.1
        | 1 => simpa using heq.2.1
        | 2 => simpa using heq.2.2.1
        | 3 => simpa using heq.2.2.2
        | m + 4 =>
          have e0 := ih m (by omega)
          have e1 := ih (m + 1) (by omega)
          have e2 := ih (m + 2) (by omega)
          have e3 := ih (m + 3) (by omega)
          have hi := (hu (i + (m + 4)) (by omega)).1
          have hj := (hu (j + (m + 4)) (by omega)).1
          have hi1 : i + (m + 4) - 1 = i + (m + 3) := by omega
          have hi2 : i + (m + 4) - 2 = i + (m + 2) := by omega
          have hi3 : i + (m + 4) - 3 = i + (m + 1) := by omega
          have hi4 : i + (m + 4) - 4 = i + m := by omega
          have hj1 : j + (m + 4) - 1 = j + (m + 3) := by omega
          have hj2 : j + (m + 4) - 2 = j + (m + 2) := by omega
          have hj3 : j + (m + 4) - 3 = j + (m + 1) := by omega
          have hj4 : j + (m + 4) - 4 = j + m := by omega
          rw [hi1, hi2, hi3, hi4] at hi
          rw [hj1, hj2, hj3, hj4] at hj
          rw [e3, e2, e1, e0] at hi
          exact_mod_cast hi.trans hj.symm
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  convert (hshift (n - i)).symm using 1 <;> omega