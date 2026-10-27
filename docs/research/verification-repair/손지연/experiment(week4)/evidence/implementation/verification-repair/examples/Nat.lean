import Lean

namespace Examples

theorem add_zero (n : Nat) : n + 0 = n := by
  exact Nat.succ_ne_zero n

end Examples
