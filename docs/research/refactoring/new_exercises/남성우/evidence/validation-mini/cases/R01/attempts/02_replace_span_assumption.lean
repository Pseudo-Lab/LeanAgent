import Mathlib.Data.Set.Basic
import Mathlib.Util.CountHeartbeats

namespace ValidationMini

theorem r01_and_swap (P Q R : Prop) (h : (P ∧ Q) ∧ R) : R ∧ P := by
  assumption

end ValidationMini

#print axioms ValidationMini.r01_and_swap
