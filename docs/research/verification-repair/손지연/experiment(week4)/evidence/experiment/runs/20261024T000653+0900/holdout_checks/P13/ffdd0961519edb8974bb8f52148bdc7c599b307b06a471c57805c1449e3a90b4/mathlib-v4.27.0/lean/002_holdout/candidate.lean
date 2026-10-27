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
  have hf : Set.Finite (Set.range f) := by
    have hs : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
      rintro _ ⟨n, rfl⟩
      have h₀ := hB n
      have h₁ := hB (n + 1)
      have h₂ := hB (n + 2)
      have h₃ := hB (n + 3)
      simp only [f, Set.mem_Icc, Prod.le_def]
      exact
        ⟨⟨h₀.1, h₁.1, h₂.1, h₃.1⟩,
          ⟨h₀.2, h₁.2, h₂.2, h₃.2⟩⟩
    have hfin : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      apply Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
      intro x hx
      simp_all [Set.mem_Icc]
    exact hfin.subset hs
  obtain ⟨i, j, hij, hfj⟩ : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! h
    have hinj : Function.Injective f := by
      intro i j hij'
      by_cases heq : i = j
      · exact heq
      · rcases (by omega : i < j ∨ j < i) with hlt | hlt
        · exact (h i j hlt hij').elim
        · exact (h j i hlt hij'.symm).elim
    exact Set.not_infinite.mpr hf (Set.infinite_range_of_injective hinj)
  have hEq :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f] using hfj
  have hseq : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        match m with
        | 0 => simpa using hEq.1
        | 1 => simpa using hEq.2.1
        | 2 => simpa using hEq.2.2.1
        | 3 => simpa using hEq.2.2.2
        | m + 4 =>
            have e₃ := ih (m + 3) (by omega)
            have e₂ := ih (m + 2) (by omega)
            have e₁ := ih (m + 1) (by omega)
            have e₀ := ih m (by omega)
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
            have hr : (u (i + (m + 4)) : ℝ) = (u (j + (m + 4)) : ℝ) := by
              rw [hi, hj]
              simp only [hi₁, hi₂, hi₃, hi₄, hj₁, hj₂, hj₃, hj₄,
                e₃, e₂, e₁, e₀]
            exact_mod_cast hr
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  calc
    u (n + (j - i)) = u (j + (n - i)) := congrArg u (by omega)
    _ = u (i + (n - i)) := (hseq (n - i)).symm
    _ = u n := congrArg u (by omega)

#check _root_.putnam_1964_a4
#print axioms _root_.putnam_1964_a4
