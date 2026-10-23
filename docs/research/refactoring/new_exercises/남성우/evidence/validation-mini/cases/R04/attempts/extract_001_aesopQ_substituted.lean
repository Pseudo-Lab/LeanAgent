import Mathlib.Data.Set.Basic
import Mathlib.Util.CountHeartbeats

namespace ValidationMini

theorem r04_inter_union {α : Type*} (s t u : Set α) (x : α) (hx : x ∈ s ∩ (t ∪ u)) :
    x ∈ (s ∩ t) ∪ (s ∩ u) := by
  simp_all only [Set.mem_inter_iff, Set.mem_union, true_and]

end ValidationMini

#print axioms ValidationMini.r04_inter_union
