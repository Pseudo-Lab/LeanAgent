by
  rcases boundedu with ⟨B, T, hbounds⟩
  have hrange : (Set.range u).Finite := by
    apply (Set.finite_Icc B T).subset
    rintro x ⟨n, rfl⟩
    exact hbounds n
  let R := {x : ℤ // x ∈ Set.range u}
  letI : Finite R := hrange
  let s : ℕ → (Fin 4 → R) := fun n i =>
    ⟨u (n + (i : ℕ)), ⟨n + (i : ℕ), rfl⟩⟩
  have hstep (a b : ℕ) (hab : s a = s b) : s (a + 1) = s (b + 1) := by
    have h0 : u a = u b := by
      simpa [s] using congrArg Subtype.val (congrFun hab (0 : Fin 4))
    have h1 : u (a + 1) = u (b + 1) := by
      simpa [s] using congrArg Subtype.val (congrFun hab (1 : Fin 4))
    have h2 : u (a + 2) = u (b + 2) := by
      simpa [s] using congrArg Subtype.val (congrFun hab (2 : Fin 4))
    have h3 : u (a + 3) = u (b + 3) := by
      simpa [s] using congrArg Subtype.val (congrFun hab (3 : Fin 4))
    have ha := (hu (a + 4) (by omega)).1
    have hb := (hu (b + 4) (by omega)).1
    have ha1 : a + 4 - 1 = a + 3 := by omega
    have ha2 : a + 4 - 2 = a + 2 := by omega
    have ha3 : a + 4 - 3 = a + 1 := by omega
    have ha4 : a + 4 - 4 = a := by omega
    have hb1 : b + 4 - 1 = b + 3 := by omega
    have hb2 : b + 4 - 2 = b + 2 := by omega
    have hb3 : b + 4 - 3 = b + 1 := by omega
    have hb4 : b + 4 - 4 = b := by omega
    rw [ha1, ha2, ha3, ha4] at ha
    rw [hb1, hb2, hb3, hb4] at hb
    rw [h3, h2, h1, h0] at ha
    have h4r : (u (a + 4) : ℝ) = (u (b + 4) : ℝ) := ha.trans hb.symm
    have h4 : u (a + 4) = u (b + 4) := by
      exact_mod_cast h4r
    apply funext
    intro i
    apply Subtype.ext
    fin_cases i <;> simp [s, Nat.add_assoc, h1, h2, h3, h4]
  obtain ⟨p, q, hpq, hs⟩ := Finite.exists_ne_map_eq_of_infinite s
  have hmain (p q : ℕ) (hpq : p < q) (hs : s p = s q) :
      ∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n := by
    have hall : ∀ k : ℕ, s (p + k) = s (q + k) := by
      intro k
      induction k with
      | zero => simpa using hs
      | succ k ih =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
            hstep (p + k) (q + k) ih
    refine ⟨p, q - p, Nat.sub_pos_of_lt hpq, ?_⟩
    intro n hn
    have hv : u (p + (n - p)) = u (q + (n - p)) := by
      simpa [s] using
        congrArg Subtype.val (congrFun (hall (n - p)) (0 : Fin 4))
    have hleft : p + (n - p) = n := by omega
    have hright : q + (n - p) = n + (q - p) := by omega
    rw [hleft, hright] at hv
    exact hv.symm
  rcases lt_or_gt_of_ne hpq with hpq | hqp
  · exact hmain p q hpq hs
  · exact hmain q p hqp hs.symm