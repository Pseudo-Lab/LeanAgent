by
  have h_main : ∃ i j : ℕ, i < j ∧
      (u i = u j ∧ u (i + 1) = u (j + 1) ∧
       u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3)) := by
    obtain ⟨B, T, hB⟩ := boundedu
    classical
    let f : ℕ → ℤ × ℤ × ℤ × ℤ :=
      fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
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
    have hfinite : Set.Finite (Set.range f) :=
      Set.Finite.subset hbox hsub
    have hrep : ∃ i j : ℕ, i < j ∧ f i = f j := by
      by_contra! h
      have hinj : Function.Injective f := by
        intro a b hab
        rcases lt_trichotomy a b with hablt | habeq | hbalt
        · exact ((h a b hablt) hab).elim
        · exact habeq
        · exact ((h b a hbalt) hab.symm).elim
      exact Set.not_infinite.mpr hfinite
        (Set.infinite_range_of_injective hinj)
    obtain ⟨i, j, hij, heq⟩ := hrep
    refine ⟨i, j, hij, ?_⟩
    simpa [f] using heq
  obtain ⟨i, j, hij, heq⟩ := h_main
  have hstep (k : ℕ) :
      (u (k + 4) : ℝ) =
        ((u (k + 3) + u (k + 2) + u (k + 1) * u k : ℝ) /
          (u (k + 3) * u (k + 2) + u (k + 1) + u k)) := by
    have e1 : k + 4 - 1 = k + 3 := by omega
    have e2 : k + 4 - 2 = k + 2 := by omega
    have e3 : k + 4 - 3 = k + 1 := by omega
    have e4 : k + 4 - 4 = k := by omega
    simpa only [e1, e2, e3, e4] using (hu (k + 4) (by omega)).1
  have hall : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        match m with
        | 0 => simpa using heq.1
        | 1 => simpa using heq.2.1
        | 2 => simpa using heq.2.2.1
        | 3 => simpa using heq.2.2.2
        | m + 4 =>
            have hi := hstep (i + m)
            have hj := hstep (j + m)
            simp only [add_assoc] at hi hj
            have h3 := ih (m + 3) (by omega)
            have h2 := ih (m + 2) (by omega)
            have h1 := ih (m + 1) (by omega)
            have h0 := ih m (by omega)
            have hr : (u (i + (m + 4)) : ℝ) = u (j + (m + 4)) := by
              rw [hi, hj, h3, h2, h1, h0]
            exact_mod_cast hr
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  calc
    u (n + (j - i)) = u (j + (n - i)) := by congr 1 <;> omega
    _ = u (i + (n - i)) := (hall (n - i)).symm
    _ = u n := by congr 1 <;> omega