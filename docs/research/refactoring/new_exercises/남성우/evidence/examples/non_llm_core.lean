import Lean

example (P : Prop) (h : P) : P := by
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  exact h.symm

example (x y : Nat) : x + y = y + x := by
  exact Nat.add_comm x y

example (x : Nat) : (x + 0) + 0 = x := by
  simp?

example (xs : List Nat) : xs ++ [] = xs := by
  simp?

example (x y z : Nat) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  omega

example (n : Nat) (h : n ≤ 3) : n < 5 := by
  omega

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.2
  · exact h.1

example (n : Nat) : ∃ m : Nat, m = n + 1 := by
  exact ⟨n + 1, rfl⟩

example (b : Bool) : (b || false) = b := by
  cases b <;> rfl

example (x y : Nat) (h : x = y) : 0 + x = y := by
  simpa using h

example (P : Prop) (h : P) : P := by
  have unused : True := by trivial
  exact h

example (P : Prop) (h : P) : P := by
  exact h

example (x y : Nat) : x + y = y + x := by
  exact?

example (x : Nat) : (x + 0) + 0 = x := by
  simp only [Nat.add_zero]
