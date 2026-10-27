import Mathlib.Data.Set.Basic
import Mathlib.Util.CountHeartbeats

namespace ValidationMini

theorem r04_inter_union {α : Type*} (s t u : Set α) (x : α) (hx : x ∈ s ∩ (t ∪ u)) :
    x ∈ (s ∩ t) ∪ (s ∩ u) := by
  aesop?

end ValidationMini

#print axioms ValidationMini.r04_inter_union
