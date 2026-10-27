import Mathlib
import Aesop

set_option maxHeartbeats 0

open Set Function


theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  classical
  obtain ⟨B, T, hB⟩ := boundedu
  let f : ℕ → ℤ × ℤ × ℤ × ℤ :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  have hf : Set.Finite (Set.range f) := by
    refine Set.Finite.subset
      (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T))) ?_
    rintro _ ⟨n, rfl⟩
    simp only [f, Set.mem_Icc, Prod.le_def]
    exact ⟨
      ⟨(hB n).1, (hB (n + 1)).1, (hB (n + 2)).1, (hB (n + 3)).1⟩,
      ⟨(hB n).2, (hB (n + 1)).2, (hB (n + 2)).2, (hB (n + 3)).2⟩⟩
  have hc : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! h
    have hinj : Function.Injective f := by
      intro i j e
      rcases lt_trichotomy i j with hij | hij | hij
      · exact (h i j hij e).elim
      · exact hij
      · exact (h j i hij e.symm).elim
    exact Set.not_infinite.mpr hf (Set.infinite_range_of_injective hinj)
  obtain ⟨i, j, hij, he⟩ := hc
  have heq :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f] using he
  rcases heq with ⟨h0, h1, h2, h3⟩
  have hs : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        rcases lt_or_ge m 4 with hm | hm
        · interval_cases m <;> simp_all
        · have p1 : u (i + m - 1) = u (j + m - 1) := by
            convert ih (m - 1) (by omega) using 1 <;> omega
          have p2 : u (i + m - 2) = u (j + m - 2) := by
            convert ih (m - 2) (by omega) using 1 <;> omega
          have p3 : u (i + m - 3) = u (j + m - 3) := by
            convert ih (m - 3) (by omega) using 1 <;> omega
          have p4 : u (i + m - 4) = u (j + m - 4) := by
            convert ih (m - 4) (by omega) using 1 <;> omega
          have hi := (hu (i + m) (by omega)).1
          have hj := (hu (j + m) (by omega)).1
          have hr : (u (i + m) : ℝ) = u (j + m) := by
            rw [hi, hj, p1, p2, p3, p4]
          exact_mod_cast hr
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  convert (hs (n - i)).symm using 1 <;> omega

#check _root_.putnam_1964_a4
#print axioms _root_.putnam_1964_a4
