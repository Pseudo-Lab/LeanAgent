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
  let f : ℕ → (ℤ × ℤ × ℤ × ℤ) :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  have hfinite : Set.Finite (Set.range f) := by
    have hsub : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
      rintro _ ⟨n, rfl⟩
      have h0 := hB n
      have h1 := hB (n + 1)
      have h2 := hB (n + 2)
      have h3 := hB (n + 3)
      simp only [f, Set.mem_Icc, Prod.le_def]
      aesop
    have hbox : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      refine Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T))) ?_
      intro x hx
      simpa [Set.mem_Icc] using hx
    exact hbox.subset hsub
  have hcollision : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! h
    have hinj : Function.Injective f := by
      intro i j hij
      rcases lt_trichotomy i j with hij' | rfl | hij'
      · exact False.elim ((h i j hij') hij)
      · rfl
      · exact False.elim ((h j i hij') hij.symm)
    have hinfinite := Set.infinite_range_of_injective hinj
    exact Set.not_infinite.mpr hfinite hinfinite
  obtain ⟨i, j, hij, hfij⟩ := hcollision
  have hstates :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f, Prod.ext_iff] using hfij
  rcases hstates with ⟨h0, h1, h2, h3⟩
  have hrec (k r : ℕ) :
      (u (k + (r + 4)) : ℝ) =
        ((u (k + (r + 3)) + u (k + (r + 2)) +
              u (k + (r + 1)) * u (k + r)) : ℝ) /
          (u (k + (r + 3)) * u (k + (r + 2)) +
            u (k + (r + 1)) + u (k + r)) := by
    convert (hu (k + (r + 4)) (by omega)).1 using 1 <;> omega
  have hshift : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        by_cases hm : m < 4
        · interval_cases m <;> simp_all [add_assoc]
        · obtain ⟨r, rfl⟩ : ∃ r, m = r + 4 := ⟨m - 4, by omega⟩
          apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
          rw [hrec i r, hrec j r,
            ih (r + 3) (by omega), ih (r + 2) (by omega),
            ih (r + 1) (by omega), ih r (by omega)]
  refine ⟨i, j - i, Nat.sub_pos_of_lt hij, ?_⟩
  intro n hn
  convert (hshift (n - i)).symm using 1 <;> omega
