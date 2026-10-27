import Mathlib.Data.Set.Basic
import Mathlib.Util.CountHeartbeats

namespace ValidationMini

theorem r01_and_swap (P Q R : Prop) (h : (P ∧ Q) ∧ R) : R ∧ P := by
  constructor
  · exact h.2
  · exact h.1.1

end ValidationMini

#print axioms ValidationMini.r01_and_swap
