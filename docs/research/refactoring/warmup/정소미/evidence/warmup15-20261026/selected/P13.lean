theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  obtain ⟨B, T, hB⟩ := boundedu
  let f n (k : Fin 4) : Icc B T := ⟨u (n+k), hB _⟩
  obtain ⟨a, b, hab, he⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := f) (by simp)
  have hp m : u (a + m) = u (b + m) := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm : m < 4
      · exact congrArg Subtype.val (congrFun he ⟨m, hm⟩)
      · apply @Int.cast_injective ℝ
        rw [(hu (a+m) (by omega)).1, (hu (b+m) (by omega)).1]
        simp (disch := omega) only [Nat.add_sub_assoc, ih]
  refine ⟨a, b-a, Nat.sub_pos_of_lt hab, fun n hn => ?_⟩
  convert (hp (n-a)).symm using 2 <;> omega
