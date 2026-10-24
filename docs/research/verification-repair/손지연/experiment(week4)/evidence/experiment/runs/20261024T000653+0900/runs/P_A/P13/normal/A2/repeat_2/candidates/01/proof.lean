by
  classical
  obtain ⟨B, T, hB⟩ := boundedu
  let f : ℕ → (ℤ × ℤ × ℤ × ℤ) :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  have hfin : Set.Finite (Set.range f) := by
    have hsub : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
      intro x hx
      rcases hx with ⟨n, rfl⟩
      have h₀ := hB n
      have h₁ := hB (n + 1)
      have h₂ := hB (n + 2)
      have h₃ := hB (n + 3)
      simp only [Set.mem_Icc, Prod.le_def] at h₀ h₁ h₂ h₃ ⊢
      constructor <;>
        (try constructor) <;>
        (try constructor) <;>
        (try constructor) <;>
        (try simp_all [f])
    have hIcc : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      apply Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
      intro x hx
      simp_all [Set.mem_Icc]
    exact hIcc.subset hsub
  have hpigeon : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! h
    have hinj : Function.Injective f := by
      intro i j hij
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · exact (h i j hlt hij).elim
      · rfl
      · exact (h j i hgt hij.symm).elim
    have hrange : Set.Infinite (Set.range f) :=
      Set.infinite_range_of_injective hinj
    exact Set.not_infinite.mpr hfin hrange
  obtain ⟨i, j, hij, hf⟩ := hpigeon
  have heq :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f] using hf
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
          have hi := (hu (i + (m + 4)) (by omega)).1
          have hj := (hu (j + (m + 4)) (by omega)).1
          have h₁ : i + (m + 4) - 1 = i + (m + 3) := by omega
          have h₂ : i + (m + 4) - 2 = i + (m + 2) := by omega
          have h₃ : i + (m + 4) - 3 = i + (m + 1) := by omega
          have h₄ : i + (m + 4) - 4 = i + m := by omega
          have h₅ : j + (m + 4) - 1 = j + (m + 3) := by omega
          have h₆ : j + (m + 4) - 2 = j + (m + 2) := by omega
          have h₇ : j + (m + 4) - 3 = j + (m + 1) := by omega
          have h₈ : j + (m + 4) - 4 = j + m := by omega
          have h₉ : u (i + (m + 3)) = u (j + (m + 3)) :=
            ih (m + 3) (by omega)
          have h₁₀ : u (i + (m + 2)) = u (j + (m + 2)) :=
            ih (m + 2) (by omega)
          have h₁₁ : u (i + (m + 1)) = u (j + (m + 1)) :=
            ih (m + 1) (by omega)
          have h₁₂ : u (i + m) = u (j + m) := ih m (by omega)
          have hreal :
              (u (i + (m + 4)) : ℝ) = (u (j + (m + 4)) : ℝ) := by
            rw [hi, hj]
            simp [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈] at *
          exact_mod_cast hreal
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  have h := (hall (n - i)).symm
  convert h using 1 <;> omega