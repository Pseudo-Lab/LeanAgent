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
  have hsub : Set.range f ⊆ Set.Icc (B, B, B, B) (T, T, T, T) := by
    rintro _ ⟨n, rfl⟩
    simp only [f, Set.mem_Icc, Prod.le_def]
    obtain ⟨hn0l, hn0u⟩ := hBT n
    obtain ⟨hn1l, hn1u⟩ := hBT (n + 1)
    obtain ⟨hn2l, hn2u⟩ := hBT (n + 2)
    obtain ⟨hn3l, hn3u⟩ := hBT (n + 3)
    exact ⟨⟨hn0l, hn1l, hn2l, hn3l⟩, ⟨hn0u, hn1u, hn2u, hn3u⟩⟩
  have hbox : Set.Finite (Set.Icc (B, B, B, B) (T, T, T, T)) := by
    apply Set.Finite.subset
      (Set.finite_mem_finset (Finset.Icc (B, B, B, B) (T, T, T, T)))
    intro x hx
    simp_all [Set.mem_Icc]
    <;> aesop
  have hfin : Set.Finite (Set.range f) := hbox.subset hsub
  have hrep : ∃ i j : ℕ, i < j ∧ f i = f j := by
    by_contra! h
    have hinj : Function.Injective f := by
      intro a b hab
      rcases lt_trichotomy a b with hab' | hab' | hab'
      · exact (h a b hab' hab).elim
      · exact hab'
      · exact (h b a hab' hab.symm).elim
    exact Set.not_infinite.mpr hfin (Set.infinite_range_of_injective hinj)
  obtain ⟨i, j, hij, hf⟩ := hrep
  have e0 : u i = u j := by
    simpa [f] using congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.1) hf
  have e1 : u (i + 1) = u (j + 1) := by
    simpa [f] using congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.2.1) hf
  have e2 : u (i + 2) = u (j + 2) := by
    simpa [f] using congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.2.2.1) hf
  have e3 : u (i + 3) = u (j + 3) := by
    simpa [f] using congrArg (fun x : ℤ × ℤ × ℤ × ℤ => x.2.2.2) hf
  have hall : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        by_cases h0 : m = 0
        · subst m
          simpa using e0
        by_cases h1 : m = 1
        · subst m
          simpa using e1
        by_cases h2 : m = 2
        · subst m
          simpa using e2
        by_cases h3 : m = 3
        · subst m
          simpa using e3
        have hm : 4 ≤ m := by omega
        have hi := (hu (i + m) (by omega)).1
        have hj := (hu (j + m) (by omega)).1
        have ai1 : i + m - 1 = i + (m - 1) := by omega
        have ai2 : i + m - 2 = i + (m - 2) := by omega
        have ai3 : i + m - 3 = i + (m - 3) := by omega
        have ai4 : i + m - 4 = i + (m - 4) := by omega
        have aj1 : j + m - 1 = j + (m - 1) := by omega
        have aj2 : j + m - 2 = j + (m - 2) := by omega
        have aj3 : j + m - 3 = j + (m - 3) := by omega
        have aj4 : j + m - 4 = j + (m - 4) := by omega
        rw [ai1, ai2, ai3, ai4] at hi
        rw [aj1, aj2, aj3, aj4] at hj
        have em1 := ih (m - 1) (by omega)
        have em2 := ih (m - 2) (by omega)
        have em3 := ih (m - 3) (by omega)
        have em4 := ih (m - 4) (by omega)
        rw [em1, em2, em3, em4] at hi
        have hc : (u (i + m) : ℝ) = u (j + m) := hi.trans hj.symm
        exact_mod_cast hc
  refine ⟨i, j - i, by omega, ?_⟩
  intro n hn
  convert (hall (n - i)).symm using 1 <;> omega

#check _root_.putnam_1964_a4
#print axioms _root_.putnam_1964_a4
