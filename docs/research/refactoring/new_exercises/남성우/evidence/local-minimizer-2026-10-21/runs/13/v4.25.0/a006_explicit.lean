import Mathlib
import Aesop

set_option maxHeartbeats 0

open Set Function



theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by 
  have h_main : ∃ (i j : ℕ), i < j ∧ (u i = u j ∧ u (i + 1) = u (j + 1) ∧ u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3)) := by
    obtain ⟨B, T, hB⟩ := boundedu
    have h₁ : ∃ (i j : ℕ), i < j ∧ (u i = u j ∧ u (i + 1) = u (j + 1) ∧ u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3)) := by
      
      classical
      
      let f : ℕ → (ℤ × ℤ × ℤ × ℤ) := fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
      have h₂ : Set.Finite (Set.range f) := by
        have h₃ : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
          intro x hx
          rcases hx with ⟨n, rfl⟩
          have h₄ := hB n
          have h₅ := hB (n + 1)
          have h₆ := hB (n + 2)
          have h₇ := hB (n + 3)
          simp only [Set.mem_Icc, Prod.le_def] at h₄ h₅ h₆ h₇ ⊢
          constructor <;>
          (try constructor) <;>
          (try constructor) <;>
          (try constructor) <;>
          (try simp_all [f]) <;>
          (try nlinarith)
        
        have h₄ : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
          apply Set.Finite.subset (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
          intro x hx
          simp_all [Set.mem_Icc]
          <;>
          (try aesop)
        exact Set.Finite.subset h₄ h₃
      
      have h₃ : ∃ (i j : ℕ), i < j ∧ f i = f j := by
        by_contra! h₄
        have h₅ : Function.Injective f := by
          intro i j h₆
          by_cases h₇ : i = j
          · exact h₇
          · have h₈ : i < j ∨ j < i := by omega
            cases h₈ with
            | inl h₈ =>
              have h₉ := h₄ i j h₈
              simp_all only [ge_iff_le, ne_eq]
            | inr h₈ =>
              have h₉ := h₄ j i h₈
              simp_all
        have h₆ : Set.Infinite (Set.range f) := Set.infinite_range_of_injective h₅
        exact Set.not_infinite.mpr h₂ h₆
      
      obtain ⟨i, j, h₄, h₅⟩ := h₃
      refine' ⟨i, j, h₄, _⟩
      simp [f] at h₅ ⊢
      <;>
      (try simp_all [Prod.ext_iff]) <;>
      (try omega) <;>
      (try aesop)
    exact h₁
  
  have h_periodic : ∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n := by
    simp only [gt_iff_lt, ge_iff_le]
  
  exact h_periodic


#print axioms putnam_1964_a4
