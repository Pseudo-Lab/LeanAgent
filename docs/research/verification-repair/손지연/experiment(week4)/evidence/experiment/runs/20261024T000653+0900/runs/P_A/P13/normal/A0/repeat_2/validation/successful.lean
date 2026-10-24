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
  let f : ℕ → (ℤ × ℤ × ℤ × ℤ) :=
    fun n => (u n, u (n + 1), u (n + 2), u (n + 3))
  obtain ⟨B, T, hB⟩ := boundedu
  have hrange : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
    rintro _ ⟨n, rfl⟩
    rcases hB n with ⟨hn₀, hn₁⟩
    rcases hB (n + 1) with ⟨hn₂, hn₃⟩
    rcases hB (n + 2) with ⟨hn₄, hn₅⟩
    rcases hB (n + 3) with ⟨hn₆, hn₇⟩
    simp only [Set.mem_Icc, Prod.le_def]
    aesop
  have hIcc : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
    apply Set.Finite.subset
      (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
    intro x hx
    simp_all [Set.mem_Icc]
  have hfinite : Set.Finite (Set.range f) := hIcc.subset hrange
  have hrepeated : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! hne
    have hinjective : Function.Injective f := by
      intro i j hij
      by_cases heq : i = j
      · exact heq
      · rcases lt_or_gt_of_ne heq with hij' | hji'
        · exact (hne i j hij' hij).elim
        · exact (hne j i hji' hij.symm).elim
    exact Set.not_infinite.mpr hfinite
      (Set.infinite_range_of_injective hinjective)
  obtain ⟨i, j, hij, hf⟩ := hrepeated
  have hstate :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f, Prod.ext_iff] using hf
  rcases hstate with ⟨h₀, h₁, h₂, h₃⟩
  have hshift : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        match m with
        | 0 => simpa using h₀
        | 1 => exact h₁
        | 2 => exact h₂
        | 3 => exact h₃
        | m + 4 =>
          have hi := (hu (i + (m + 4)) (by omega)).1
          have hj := (hu (j + (m + 4)) (by omega)).1
          rw [show i + (m + 4) - 1 = i + (m + 3) by omega,
              show i + (m + 4) - 2 = i + (m + 2) by omega,
              show i + (m + 4) - 3 = i + (m + 1) by omega,
              show i + (m + 4) - 4 = i + m by omega] at hi
          rw [show j + (m + 4) - 1 = j + (m + 3) by omega,
              show j + (m + 4) - 2 = j + (m + 2) by omega,
              show j + (m + 4) - 3 = j + (m + 1) by omega,
              show j + (m + 4) - 4 = j + m by omega] at hj
          have e₃ := ih (m + 3) (by omega)
          have e₂ := ih (m + 2) (by omega)
          have e₁ := ih (m + 1) (by omega)
          have e₀ := ih m (by omega)
          rw [e₃, e₂, e₁, e₀] at hi
          have hc : (u (i + (m + 4)) : ℝ) = u (j + (m + 4)) :=
            hi.trans hj.symm
          exact_mod_cast hc
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  have h := hshift (n - i)
  have hin : i + (n - i) = n := by omega
  have hjn : j + (n - i) = n + (j - i) := by omega
  rw [hin, hjn] at h
  exact h.symm
