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
    obtain ⟨i, j, hij, h_eq⟩ := h_main
    have h₁ : ∀ m : ℕ, u (i + m) = u (j + m) := by
      intro m
      have h₂ : ∀ m : ℕ, u (i + m) = u (j + m) := by
        intro m
        induction m using Nat.strong_induction_on with
        | h m ih =>
          match m with
          | 0 => simpa using h_eq.1
          | 1 => simpa using h_eq.2.1
          | 2 => simpa using h_eq.2.2.1
          | 3 => simpa using h_eq.2.2.2
          | m + 4 =>
            have h₃ : i + (m + 4) ≥ 4 := by
              have h₄ : i ≥ 0 := by linarith
              omega
            have h₄ : u (i + (m + 4)) = ((u (i + (m + 4) - 1) + u (i + (m + 4) - 2) + u (i + (m + 4) - 3) * u (i + (m + 4) - 4)) : ℝ) / (u (i + (m + 4) - 1) * u (i + (m + 4) - 2) + u (i + (m + 4) - 3) + u (i + (m + 4) - 4)) := by
              have h₅ := hu (i + (m + 4)) (by omega)
              have h₆ := h₅.1
              norm_cast at h₆ ⊢
              <;> simp_all [add_assoc]
              <;> ring_nf at *
              <;> norm_num at *
              <;> linarith
            have h₅ : u (j + (m + 4)) = ((u (j + (m + 4) - 1) + u (j + (m + 4) - 2) + u (j + (m + 4) - 3) * u (j + (m + 4) - 4)) : ℝ) / (u (j + (m + 4) - 1) * u (j + (m + 4) - 2) + u (j + (m + 4) - 3) + u (j + (m + 4) - 4)) := by
              have h₆ := hu (j + (m + 4)) (by
                have h₇ : j ≥ i + 1 := by omega
                omega
              )
              have h₇ := h₆.1
              norm_cast at h₇ ⊢
              <;> simp_all [add_assoc]
              <;> ring_nf at *
              <;> norm_num at *
              <;> linarith
            have h₆ : (i + (m + 4) - 1 : ℕ) = i + (m + 3) := by
              omega
            have h₇ : (i + (m + 4) - 2 : ℕ) = i + (m + 2) := by
              omega
            have h₈ : (i + (m + 4) - 3 : ℕ) = i + (m + 1) := by
              omega
            have h₉ : (i + (m + 4) - 4 : ℕ) = i + m := by
              omega
            have h₁₀ : (j + (m + 4) - 1 : ℕ) = j + (m + 3) := by
              omega
            have h₁₁ : (j + (m + 4) - 2 : ℕ) = j + (m + 2) := by
              omega
            have h₁₂ : (j + (m + 4) - 3 : ℕ) = j + (m + 1) := by
              omega
            have h₁₃ : (j + (m + 4) - 4 : ℕ) = j + m := by
              omega
            have h₁₄ : u (i + (m + 3)) = u (j + (m + 3)) := by
              have h₁₅ := ih (m + 3) (by omega)
              simp [add_assoc] at h₁₅ ⊢
              <;> omega
            have h₁₅ : u (i + (m + 2)) = u (j + (m + 2)) := by
              have h₁₆ := ih (m + 2) (by omega)
              simp [add_assoc] at h₁₆ ⊢
              <;> omega
            have h₁₆ : u (i + (m + 1)) = u (j + (m + 1)) := by
              have h₁₇ := ih (m + 1) (by omega)
              simp [add_assoc] at h₁₇ ⊢
              <;> omega
            have h₁₇ : u (i + m) = u (j + m) := by
              have h₁₈ := ih m (by omega)
              simp [add_assoc] at h₁₈ ⊢
              <;> omega
            have h₁₈ : (u (i + (m + 4)) : ℝ) = (u (j + (m + 4)) : ℝ) := by
              rw [h₄, h₅]
              simp [h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃] at *
              norm_cast at *
              <;>
              (try simp_all [h₁₄, h₁₅, h₁₆, h₁₇]) <;>
              (try ring_nf at *) <;>
              (try field_simp at *) <;>
              (try norm_cast at *) <;>
              (try linarith)
            norm_cast at h₁₈ ⊢
            <;>
            (try simp_all) <;>
            (try linarith)
      exact h₂ m
    have h₂ : ∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n := by
      use i, (j - i)
      have h₃ : j - i > 0 := by
        omega
      constructor
      · exact h₃
      · intro n hn
        have h₄ : u (n + (j - i)) = u n := by
          have h₅ : u (i + (n - i)) = u (j + (n - i)) := by
            have h₆ := h₁ (n - i)
            simp [add_assoc] at h₆ ⊢
            <;> omega
          have h₆ : i + (n - i) = n := by
            omega
          have h₇ : j + (n - i) = n + (j - i) := by
            omega
          rw [h₆] at h₅
          rw [h₇] at h₅
          linarith
        exact h₄
    exact h₂
  
  exact h_periodic


#print axioms putnam_1964_a4
