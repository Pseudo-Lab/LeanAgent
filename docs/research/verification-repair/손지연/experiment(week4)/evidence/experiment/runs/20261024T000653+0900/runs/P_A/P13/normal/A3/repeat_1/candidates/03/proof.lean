by
  classical
  obtain ⟨B, T, hB⟩ := boundedu
  let f : ℕ → ℤ × ℤ × ℤ × ℤ := fun n =>
    (u n, u (n + 1), u (n + 2), u (n + 3))
  have hf : Set.Finite (Set.range f) := by
    apply (Set.finite_mem_finset
      (Finset.Icc (B, B, B, B) (T, T, T, T))).subset
    rintro _ ⟨n, rfl⟩
    simp only [Finset.mem_Icc, Prod.le_def]
    exact ⟨⟨(hB n).1, (hB (n + 1)).1, (hB (n + 2)).1, (hB (n + 3)).1⟩,
      (hB n).2, (hB (n + 1)).2, (hB (n + 2)).2, (hB (n + 3)).2⟩
  obtain ⟨i, j, hij, hfij⟩ : ∃ i j, i < j ∧ f i = f j := by
    by_contra! h
    exact (Set.infinite_range_of_injective (fun i j e => by
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact (h i j hij e).elim
      · rfl
      · exact (h j i hji e.symm).elim)) hf
  have hrec (a : ℕ) :
      (u (a + 4) : ℝ) =
        ((u (a + 3) + u (a + 2) + u (a + 1) * u a) : ℝ) /
          (u (a + 3) * u (a + 2) + u (a + 1) + u a) := by
    simpa only [show a + 4 - 1 = a + 3 by omega,
      show a + 4 - 2 = a + 2 by omega,
      show a + 4 - 3 = a + 1 by omega,
      show a + 4 - 4 = a by omega] using (hu (a + 4) (by omega)).1
  have hstep {a b : ℕ} (h : f a = f b) : f (a + 1) = f (b + 1) := by
    obtain ⟨h0, h1, h2, h3⟩ :
        u a = u b ∧ u (a + 1) = u (b + 1) ∧
          u (a + 2) = u (b + 2) ∧ u (a + 3) = u (b + 3) := by
      simpa [f] using h
    have h4 : u (a + 4) = u (b + 4) := by
      exact_mod_cast (show (u (a + 4) : ℝ) = u (b + 4) by
        rw [hrec a, hrec b, h3, h2, h1, h0])
    change (u (a + 1), u (a + 2), u (a + 3), u (a + 4)) =
      (u (b + 1), u (b + 2), u (b + 3), u (b + 4))
    rw [h1, h2, h3, h4]
  have hs : ∀ k, f (i + k) = f (j + k) := by
    intro k
    induction k with
    | zero => simpa using hfij
    | succ k ih => exact hstep ih
  have hseq (m : ℕ) : u (i + m) = u (j + m) := by
    simpa [f] using congrArg Prod.fst (hs m)
  refine ⟨i, j - i, by omega, fun n hn => ?_⟩
  convert (hseq (n - i)).symm using 1 <;> omega