import Mathlib.Data.Set.Basic
import Mathlib.Util.CountHeartbeats

namespace ValidationMini

theorem r01_and_swap (P Q R : Prop) (h : (P ∧ Q) ∧ R) : R ∧ P := by
  trace_state
  exact ⟨h.1.1, h.2⟩

end ValidationMini
