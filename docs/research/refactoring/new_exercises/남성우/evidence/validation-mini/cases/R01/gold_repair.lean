import Mathlib.Data.Set.Basic
import Mathlib.Util.CountHeartbeats

namespace ValidationMini

theorem r01_and_swap (P Q R : Prop) (h : (P ∧ Q) ∧ R) : R ∧ P := by
  exact ⟨h.2, h.1.1⟩

end ValidationMini
