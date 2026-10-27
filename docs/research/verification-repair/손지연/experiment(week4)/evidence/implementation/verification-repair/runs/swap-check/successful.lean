import Lean

namespace Examples

theorem and_swap (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  apply And.intro
  exact h.2
  exact h.1


end Examples
