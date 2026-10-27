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
  let f : ℕ → ℤ × ℤ × ℤ × ℤ := fun n =>
    (u n, u (n + 1), u (n + 2), u (n + 3))
  have hf : Set.Finite (Set.range f) := by
    have hbox : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      apply Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
      intro x hx
      simpa [Set.mem_Icc] using hx
    apply hbox.subset
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_Icc, Prod.le_def]
    have h0 := hB n
    have h1 := hB (n + 1)
    have h2 := hB (n + 2)
    have h3 := hB (n + 3)
    aesop
  have hrep : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! h
    have hinj : Function.Injective f := by
      intro i j hij
      rcases lt_trichotomy i j with hij' | rfl | hji
      · exact (h i j hij' hij).elim
      · rfl
      · exact (h j i hji hij.symm).elim
    have hi := Set.infinite_range_of_injective hinj
    exact hi hf
  obtain ⟨i, j, hij, hfij⟩ := hrep
  have heq :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f] using hfij
  rcases heq with ⟨h0, h1, h2, h3⟩
  have hrec (a k : ℕ) :
      (u (a + (k + 4)) : ℝ) =
        ((u (a + (k + 3)) + u (a + (k + 2)) +
            u (a + (k + 1)) * u (a + k)) : ℝ) /
          (u (a + (k + 3)) * u (a + (k + 2)) +
            u (a + (k + 1)) + u (a + k)) := by
    have e1 : a + (k + 4) - 1 = a + (k + 3) := by omega
    have e2 : a + (k + 4) - 2 = a + (k + 2) := by omega
    have e3 : a + (k + 4) - 3 = a + (k + 1) := by omega
    have e4 : a + (k + 4) - 4 = a + k := by omega
    simpa only [e1, e2, e3, e4] using (hu (a + (k + 4)) (by omega)).1
  have hseq : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        match m with
        | 0 => simpa using h0
        | 1 => exact h1
        | 2 => exact h2
        | 3 => exact h3
        | k + 4 =>
            have H : (u (i + (k + 4)) : ℝ) = (u (j + (k + 4)) : ℝ) := by
              rw [hrec i k, hrec j k]
              rw [ih (k + 3) (by omega), ih (k + 2) (by omega),
                ih (k + 1) (by omega), ih k (by omega)]
            exact_mod_cast H
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  calc
    u (n + (j - i)) = u (j + (n - i)) := congrArg u (by omega)
    _ = u (i + (n - i)) := (hseq (n - i)).symm
    _ = u n := congrArg u (by omega)
