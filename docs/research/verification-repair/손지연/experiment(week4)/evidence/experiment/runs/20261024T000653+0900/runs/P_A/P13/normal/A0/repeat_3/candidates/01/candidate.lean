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
  have hbox :
      (Set.Icc (B, B, B, B) (T, T, T, T) :
        Set (ℤ × ℤ × ℤ × ℤ)).Finite := by
    apply Set.Finite.subset
      (Set.finite_mem_finset
        (Finset.Icc (B, B, B, B) (T, T, T, T)))
    intro x hx
    simp_all [Set.mem_Icc]
    <;> aesop
  have hfin : (Set.range f).Finite := by
    apply Set.Finite.subset hbox
    rintro _ ⟨n, rfl⟩
    have h0 := hBT n
    have h1 := hBT (n + 1)
    have h2 := hBT (n + 2)
    have h3 := hBT (n + 3)
    simp only [f, Set.mem_Icc, Prod.le_def]
    aesop
  have hrep : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! h
    have hinj : Function.Injective f := by
      intro a b hab
      rcases lt_trichotomy a b with hablt | rfl | hbalt
      · exact (h a b hablt hab).elim
      · rfl
      · exact (h b a hbalt hab.symm).elim
    have hinf : Set.Infinite (Set.range f) :=
      Set.infinite_range_of_injective hinj
    exact Set.not_infinite.mpr hfin hinf
  obtain ⟨i, j, hij, hfj⟩ := hrep
  have heq :
      u i = u j ∧
      u (i + 1) = u (j + 1) ∧
      u (i + 2) = u (j + 2) ∧
      u (i + 3) = u (j + 3) := by
    simpa [f, Prod.ext_iff] using hfj
  have hseq : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        by_cases hm : m < 4
        · interval_cases m <;> simp_all
        · have e1 : u (i + m - 1) = u (j + m - 1) := by
            convert ih (m - 1) (by omega) using 1 <;> omega
          have e2 : u (i + m - 2) = u (j + m - 2) := by
            convert ih (m - 2) (by omega) using 1 <;> omega
          have e3 : u (i + m - 3) = u (j + m - 3) := by
            convert ih (m - 3) (by omega) using 1 <;> omega
          have e4 : u (i + m - 4) = u (j + m - 4) := by
            convert ih (m - 4) (by omega) using 1 <;> omega
          have hi := (hu (i + m) (by omega)).1
          have hj := (hu (j + m) (by omega)).1
          rw [e1, e2, e3, e4] at hi
          have hc : (u (i + m) : ℝ) = u (j + m) :=
            hi.trans hj.symm
          exact_mod_cast hc
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  have h := hseq (n - i)
  have hi : i + (n - i) = n := by omega
  have hj : j + (n - i) = n + (j - i) := by omega
  rw [hi, hj] at h
  exact h.symm
