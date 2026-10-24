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
  obtain ⟨B, T, hBT⟩ := boundedu
  let f : ℕ → (ℤ × ℤ × ℤ × ℤ) :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  have hfin : Set.Finite (Set.range f) := by
    apply Set.Finite.subset
      (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
    rintro _ ⟨n, rfl⟩
    have h₀ := hBT n
    have h₁ := hBT (n + 1)
    have h₂ := hBT (n + 2)
    have h₃ := hBT (n + 3)
    simp only [f, Finset.mem_Icc, Prod.le_def]
    aesop
  have hcollision : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! h
    have hinj : Function.Injective f := by
      intro i j hij
      rcases lt_trichotomy i j with hij' | rfl | hji
      · exact (h i j hij' hij).elim
      · rfl
      · exact (h j i hji hij.symm).elim
    exact Set.not_infinite.mpr hfin (Set.infinite_range_of_injective hinj)
  obtain ⟨i, j, hij, hf⟩ := hcollision
  have hs :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f, Prod.ext_iff] using hf
  rcases hs with ⟨h₀, h₁, h₂, h₃⟩
  have hshift : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        by_cases hm : m < 4
        · interval_cases m <;> simp_all
        · have hm' : 4 ≤ m := by omega
          have e₁ := ih (m - 1) (by omega)
          have e₂ := ih (m - 2) (by omega)
          have e₃ := ih (m - 3) (by omega)
          have e₄ := ih (m - 4) (by omega)
          have hi := (hu (i + m) (by omega)).1
          have hj := (hu (j + m) (by omega)).1
          have ai₁ : i + m - 1 = i + (m - 1) := by omega
          have ai₂ : i + m - 2 = i + (m - 2) := by omega
          have ai₃ : i + m - 3 = i + (m - 3) := by omega
          have ai₄ : i + m - 4 = i + (m - 4) := by omega
          have aj₁ : j + m - 1 = j + (m - 1) := by omega
          have aj₂ : j + m - 2 = j + (m - 2) := by omega
          have aj₃ : j + m - 3 = j + (m - 3) := by omega
          have aj₄ : j + m - 4 = j + (m - 4) := by omega
          rw [ai₁, ai₂, ai₃, ai₄] at hi
          rw [aj₁, aj₂, aj₃, aj₄] at hj
          have hr : (u (i + m) : ℝ) = (u (j + m) : ℝ) := by
            rw [hi, hj, e₁, e₂, e₃, e₄]
          exact_mod_cast hr
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  convert (hshift (n - i)).symm using 1 <;> omega
