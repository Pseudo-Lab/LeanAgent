by
  classical
  let f : ℕ → (ℤ × ℤ × ℤ × ℤ) :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  obtain ⟨B, T, hB⟩ := boundedu
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
        (try simp_all [f]) <;>
        (try nlinarith)
    have hbox : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      apply Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
      intro x hx
      simp_all [Set.mem_Icc]
      <;> try aesop
    exact hbox.subset hsub
  have hrepeat : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! hne
    have hinj : Function.Injective f := by
      intro i j hij
      by_contra h
      rcases lt_or_gt_of_ne h with hlt | hlt
      · exact hne i j hlt hij
      · exact hne j i hlt hij.symm
    exact (Set.not_infinite.mpr hfin) (Set.infinite_range_of_injective hinj)
  obtain ⟨i, j, hij, heq⟩ := hrepeat
  have hstate :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f, Prod.ext_iff] using heq
  have hp : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      match m with
      | 0 => simpa using hstate.1
      | 1 => simpa using hstate.2.1
      | 2 => simpa using hstate.2.2.1
      | 3 => simpa using hstate.2.2.2
      | m + 4 =>
        have hi := (hu (i + (m + 4)) (by omega)).1
        have hj := (hu (j + (m + 4)) (by omega)).1
        have hi₁ : i + (m + 4) - 1 = i + (m + 3) := by omega
        have hi₂ : i + (m + 4) - 2 = i + (m + 2) := by omega
        have hi₃ : i + (m + 4) - 3 = i + (m + 1) := by omega
        have hi₄ : i + (m + 4) - 4 = i + m := by omega
        have hj₁ : j + (m + 4) - 1 = j + (m + 3) := by omega
        have hj₂ : j + (m + 4) - 2 = j + (m + 2) := by omega
        have hj₃ : j + (m + 4) - 3 = j + (m + 1) := by omega
        have hj₄ : j + (m + 4) - 4 = j + m := by omega
        simp only [hi₁, hi₂, hi₃, hi₄] at hi
        simp only [hj₁, hj₂, hj₃, hj₄] at hj
        rw [ih (m + 3) (by omega), ih (m + 2) (by omega),
          ih (m + 1) (by omega), ih m (by omega)] at hi
        have hcast :
            (u (i + (m + 4)) : ℝ) = (u (j + (m + 4)) : ℝ) :=
          hi.trans hj.symm
        exact_mod_cast hcast
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  convert (hp (n - i)).symm using 1 <;> omega