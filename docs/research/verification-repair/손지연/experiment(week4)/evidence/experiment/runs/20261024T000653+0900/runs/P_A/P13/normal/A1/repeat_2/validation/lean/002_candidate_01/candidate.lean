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
    have hsub : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
      rintro _ ⟨n, rfl⟩
      have hb₀ := hB n
      have hb₁ := hB (n + 1)
      have hb₂ := hB (n + 2)
      have hb₃ := hB (n + 3)
      simp only [Set.mem_Icc, Prod.le_def]
      aesop
    have hI : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      apply Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
      intro x hx
      simpa [Set.mem_Icc] using hx
    exact hI.subset hsub
  have hcollision : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! hne
    have hinj : Function.Injective f := by
      intro a b hab
      by_contra habn
      rcases lt_or_gt_of_ne habn with hablt | hbalt
      · exact (hne a b hablt) hab
      · exact (hne b a hbalt) hab.symm
    exact Set.not_infinite.mpr hf (Set.infinite_range_of_injective hinj)
  obtain ⟨i, j, hij, hfij⟩ := hcollision
  have h₀ : u i = u j := by
    simpa [f] using
      congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.1) hfij
  have h₁ : u (i + 1) = u (j + 1) := by
    simpa [f] using
      congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.2.1) hfij
  have h₂ : u (i + 2) = u (j + 2) := by
    simpa [f] using
      congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.2.2.1) hfij
  have h₃ : u (i + 3) = u (j + 3) := by
    simpa [f] using
      congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.2.2.2) hfij
  have htail : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        by_cases hm : m < 4
        · interval_cases m
          · simpa using h₀
          · simpa using h₁
          · simpa using h₂
          · simpa using h₃
        · have e₁ : u (i + m - 1) = u (j + m - 1) := by
            convert ih (m - 1) (by omega) using 1 <;> omega
          have e₂ : u (i + m - 2) = u (j + m - 2) := by
            convert ih (m - 2) (by omega) using 1 <;> omega
          have e₃ : u (i + m - 3) = u (j + m - 3) := by
            convert ih (m - 3) (by omega) using 1 <;> omega
          have e₄ : u (i + m - 4) = u (j + m - 4) := by
            convert ih (m - 4) (by omega) using 1 <;> omega
          have hmcast : (u (i + m) : ℝ) = (u (j + m) : ℝ) := by
            rw [(hu (i + m) (by omega)).1, (hu (j + m) (by omega)).1]
            rw [e₁, e₂, e₃, e₄]
          exact_mod_cast hmcast
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  convert (htail (n - i)).symm using 1 <;> omega

#check _root_.putnam_1964_a4
#print axioms _root_.putnam_1964_a4
