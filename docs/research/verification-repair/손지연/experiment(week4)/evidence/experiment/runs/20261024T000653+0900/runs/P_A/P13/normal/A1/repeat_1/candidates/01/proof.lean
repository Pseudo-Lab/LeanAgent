by
  classical
  obtain ⟨B, T, hB⟩ := boundedu
  let f : ℕ → ℤ × ℤ × ℤ × ℤ :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  have hf : (Set.range f).Finite := by
    have hsub : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
      rintro _ ⟨n, rfl⟩
      have h0 := hB n
      have h1 := hB (n + 1)
      have h2 := hB (n + 2)
      have h3 := hB (n + 3)
      simp only [Set.mem_Icc, Prod.le_def] at h0 h1 h2 h3 ⊢
      aesop
    apply Set.Finite.subset
      (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
    intro x hx
    simp_all [Set.mem_Icc]
  have hcollision : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! hne
    have hinj : Function.Injective f := by
      intro i j hij
      by_cases heq : i = j
      · exact heq
      · have hlt : i < j ∨ j < i := by omega
        cases hlt with
        | inl hlt => exact False.elim ((hne i j hlt) hij)
        | inr hlt => exact False.elim ((hne j i hlt) hij.symm)
    exact Set.not_infinite.mpr hf (Set.infinite_range_of_injective hinj)
  obtain ⟨i, j, hij, heq⟩ := hcollision
  have hstate :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f, Prod.ext_iff] using heq
  have hshift : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      match m with
      | 0 => simpa using hstate.1
      | 1 => simpa using hstate.2.1
      | 2 => simpa using hstate.2.2.1
      | 3 => simpa using hstate.2.2.2
      | m + 4 =>
        have e0 := ih m (by omega)
        have e1 := ih (m + 1) (by omega)
        have e2 := ih (m + 2) (by omega)
        have e3 := ih (m + 3) (by omega)
        have hi := (hu (i + (m + 4)) (by omega)).1
        have hj := (hu (j + (m + 4)) (by omega)).1
        simp only [
          show i + (m + 4) - 1 = i + (m + 3) by omega,
          show i + (m + 4) - 2 = i + (m + 2) by omega,
          show i + (m + 4) - 3 = i + (m + 1) by omega,
          show i + (m + 4) - 4 = i + m by omega] at hi
        simp only [
          show j + (m + 4) - 1 = j + (m + 3) by omega,
          show j + (m + 4) - 2 = j + (m + 2) by omega,
          show j + (m + 4) - 3 = j + (m + 1) by omega,
          show j + (m + 4) - 4 = j + m by omega] at hj
        have hc : (u (i + (m + 4)) : ℝ) = (u (j + (m + 4)) : ℝ) := by
          rw [hi, hj, e3, e2, e1, e0]
        exact_mod_cast hc
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  have hleft : i + (n - i) = n := by omega
  have hright : j + (n - i) = n + (j - i) := by omega
  simpa only [hleft, hright] using (hshift (n - i)).symm