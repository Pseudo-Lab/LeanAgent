by
  classical
  obtain ⟨B, T, hB⟩ := boundedu
  let f : ℕ → (ℤ × ℤ × ℤ × ℤ) :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  have hfin : Set.Finite (Set.range f) := by
    apply Set.Finite.subset
      (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
    rintro _ ⟨n, rfl⟩
    have h₀ := hB n
    have h₁ := hB (n + 1)
    have h₂ := hB (n + 2)
    have h₃ := hB (n + 3)
    simp only [Finset.mem_Icc, Prod.le_def] at *
    simp_all [f]
  have hpigeon : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! h
    have hinj : Function.Injective f := by
      intro i j hij
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · exact (h i j hlt hij).elim
      · rfl
      · exact (h j i hgt hij.symm).elim
    exact Set.not_infinite.mpr hfin (Set.infinite_range_of_injective hinj)
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
          simp only [h₁, h₂, h₃, h₄] at hi
          simp only [h₅, h₆, h₇, h₈] at hj
          have h₉ := ih (m + 3) (by omega)
          have h₁₀ := ih (m + 2) (by omega)
          have h₁₁ := ih (m + 1) (by omega)
          have h₁₂ := ih m (by omega)
          rw [h₉, h₁₀, h₁₁, h₁₂] at hi
          exact_mod_cast hi.trans hj.symm
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  calc
    u (n + (j - i)) = u (j + (n - i)) := congrArg u (by omega)
    _ = u (i + (n - i)) := (hall (n - i)).symm
    _ = u n := congrArg u (by omega)