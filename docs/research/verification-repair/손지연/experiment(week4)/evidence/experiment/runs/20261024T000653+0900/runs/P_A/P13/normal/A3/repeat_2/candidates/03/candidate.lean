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
  have hfin : Set.Finite (Set.range f) := by
    have hsub : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
      rintro _ ⟨n, rfl⟩
      have h0 := hB n
      have h1 := hB (n + 1)
      have h2 := hB (n + 2)
      have h3 := hB (n + 3)
      simp only [f, Set.mem_Icc, Prod.le_def]
      aesop
    have hbox : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      apply Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
      intro x hx
      simpa only [Set.mem_Icc, Finset.mem_Icc] using hx
    exact hbox.subset hsub
  have hrep : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! hn
    have hinj : Function.Injective f := by
      intro a b hab
      rcases lt_trichotomy a b with h | h | h
      · exact (hn a b h hab).elim
      · exact h
      · exact (hn b a h hab.symm).elim
    exact Set.not_infinite.mpr hfin (Set.infinite_range_of_injective hinj)
  obtain ⟨i, j, hij, hf⟩ := hrep
  have heq :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f] using hf
  rcases heq with ⟨h0, h1, h2, h3⟩
  have hseq : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm : m < 4
      · interval_cases m
        · simpa using h0
        · simpa using h1
        · simpa using h2
        · simpa using h3
      · have hm4 : 4 ≤ m := by omega
        have hi := (hu (i + m) (by omega)).1
        have hj := (hu (j + m) (by omega)).1
        rw [show i + m - 1 = i + (m - 1) by omega,
            show i + m - 2 = i + (m - 2) by omega,
            show i + m - 3 = i + (m - 3) by omega,
            show i + m - 4 = i + (m - 4) by omega] at hi
        rw [show j + m - 1 = j + (m - 1) by omega,
            show j + m - 2 = j + (m - 2) by omega,
            show j + m - 3 = j + (m - 3) by omega,
            show j + m - 4 = j + (m - 4) by omega] at hj
        have e1 := ih (m - 1) (by omega)
        have e2 := ih (m - 2) (by omega)
        have e3 := ih (m - 3) (by omega)
        have e4 := ih (m - 4) (by omega)
        rw [e1, e2, e3, e4] at hi
        have hreal := hi.trans hj.symm
        exact_mod_cast hreal
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  have ha : i + (n - i) = n := by omega
  have hb : j + (n - i) = n + (j - i) := by omega
  simpa only [ha, hb] using (hseq (n - i)).symm
