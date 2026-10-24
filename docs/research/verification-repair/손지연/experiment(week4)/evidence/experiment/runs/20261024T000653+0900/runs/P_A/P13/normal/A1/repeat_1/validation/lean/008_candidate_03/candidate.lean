import Mathlib
import Aesop

set_option maxHeartbeats 0

open Set Function


theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  obtain ⟨B, T, hB⟩ := boundedu
  let f : ℕ → (ℤ × ℤ × ℤ × ℤ) :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  have hfinite : Set.Finite (Set.range f) := by
    have hsub : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
      rintro _ ⟨n, rfl⟩
      rcases hB n with ⟨hn₀, hn₁⟩
      rcases hB (n + 1) with ⟨hn₂, hn₃⟩
      rcases hB (n + 2) with ⟨hn₄, hn₅⟩
      rcases hB (n + 3) with ⟨hn₆, hn₇⟩
      simp only [Set.mem_Icc, Prod.le_def]
      exact ⟨⟨hn₀, hn₂, hn₄, hn₆⟩, ⟨hn₁, hn₃, hn₅, hn₇⟩⟩
    have hI : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      apply Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
      intro x hx
      simpa [Set.mem_Icc] using hx
    exact hI.subset hsub
  have hp : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! hcollision
    have hinj : Function.Injective f := by
      intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (hcollision a b hlt) hab
      · exact (hcollision b a hgt) hab.symm
    exact Set.not_infinite.mpr hfinite (Set.infinite_range_of_injective hinj)
  obtain ⟨i, j, hij, hf⟩ := hp
  have hstate :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f, Prod.ext_iff] using hf
  rcases hstate with ⟨h₀, h₁, h₂, h₃⟩
  have hs : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        match m with
        | 0 => simpa using h₀
        | 1 => simpa using h₁
        | 2 => simpa using h₂
        | 3 => simpa using h₃
        | m + 4 =>
            have e₁ : u (i + (m + 4) - 1) = u (j + (m + 4) - 1) := by
              convert ih (m + 3) (by omega) using 1 <;> omega
            have e₂ : u (i + (m + 4) - 2) = u (j + (m + 4) - 2) := by
              convert ih (m + 2) (by omega) using 1 <;> omega
            have e₃ : u (i + (m + 4) - 3) = u (j + (m + 4) - 3) := by
              convert ih (m + 1) (by omega) using 1 <;> omega
            have e₄ : u (i + (m + 4) - 4) = u (j + (m + 4) - 4) := by
              convert ih m (by omega) using 1 <;> omega
            have hi := (hu (i + (m + 4)) (by omega)).1
            have hj := (hu (j + (m + 4)) (by omega)).1
            have heq :
                (u (i + (m + 4)) : ℝ) = u (j + (m + 4)) := by
              rw [hi, hj, e₁, e₂, e₃, e₄]
            exact_mod_cast heq
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  convert (hs (n - i)).symm using 1 <;> omega

#check _root_.putnam_1964_a4
#print axioms _root_.putnam_1964_a4
