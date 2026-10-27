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
  have hfin : Set.Finite (Set.range f) := by
    have hbox : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
      apply Set.Finite.subset
        (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
      intro x hx
      simp_all [Set.mem_Icc]
    refine hbox.subset ?_
    rintro _ ⟨n, rfl⟩
    have h0 := hB n
    have h1 := hB (n + 1)
    have h2 := hB (n + 2)
    have h3 := hB (n + 3)
    simp only [Set.mem_Icc, Prod.le_def, f]
    aesop
  have hcollision : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! hne
    have hinj : Function.Injective f := by
      intro a b hab
      rcases lt_trichotomy a b with hlt | heq | hgt
      · exact (hne a b hlt hab).elim
      · exact heq
      · exact (hne b a hgt hab.symm).elim
    have hir : Set.Infinite (Set.range f) :=
      Set.infinite_range_of_injective hinj
    exact Set.not_infinite.mpr hfin hir
  obtain ⟨i, j, hij, hfij⟩ := hcollision
  have hbase :
      u i = u j ∧ u (i + 1) = u (j + 1) ∧
        u (i + 2) = u (j + 2) ∧ u (i + 3) = u (j + 3) := by
    simpa [f] using hfij
  have hall : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      match m with
      | 0 => simpa using hbase.1
      | 1 => simpa using hbase.2.1
      | 2 => simpa using hbase.2.2.1
      | 3 => simpa using hbase.2.2.2
      | m + 4 =>
        have hi := (hu (i + (m + 4)) (by omega)).1
        have hj := (hu (j + (m + 4)) (by omega)).1
        simp only [
          show i + (m + 4) - 1 = i + (m + 3) by omega,
          show i + (m + 4) - 2 = i + (m + 2) by omega,
          show i + (m + 4) - 3 = i + (m + 1) by omega,
          show i + (m + 4) - 4 = i + m by omega
        ] at hi
        simp only [
          show j + (m + 4) - 1 = j + (m + 3) by omega,
          show j + (m + 4) - 2 = j + (m + 2) by omega,
          show j + (m + 4) - 3 = j + (m + 1) by omega,
          show j + (m + 4) - 4 = j + m by omega
        ] at hj
        have e3 := ih (m + 3) (by omega)
        have e2 := ih (m + 2) (by omega)
        have e1 := ih (m + 1) (by omega)
        have e0 := ih m (by omega)
        rw [e3, e2, e1, e0] at hi
        exact_mod_cast hi.trans hj.symm
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  calc
    u (n + (j - i)) = u (j + (n - i)) := congrArg u (by omega)
    _ = u (i + (n - i)) := (hall (n - i)).symm
    _ = u n := congrArg u (by omega)
