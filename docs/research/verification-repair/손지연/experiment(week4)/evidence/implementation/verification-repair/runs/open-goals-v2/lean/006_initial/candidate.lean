import Lean

namespace Examples

theorem and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  skip


end Examples

#check _root_.Examples.and_swap
#print axioms _root_.Examples.and_swap
