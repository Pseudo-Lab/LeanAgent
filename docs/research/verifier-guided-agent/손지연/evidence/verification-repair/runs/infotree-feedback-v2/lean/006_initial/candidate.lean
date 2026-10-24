import Lean

namespace Examples

theorem and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  apply And.intro
  exact h.1
  exact h.1

end Examples

#check _root_.Examples.and_swap
#print axioms _root_.Examples.and_swap
