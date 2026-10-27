import Mathlib.Data.Set.Basic
import Mathlib.Util.CountHeartbeats

namespace ValidationMini

theorem r05_mem_cons (x a : ℕ) (l : List ℕ) (h : x ∈ l) : x ∈ a :: l := by
  simp only [List.mem_cons]
  right
  exact h

end ValidationMini
