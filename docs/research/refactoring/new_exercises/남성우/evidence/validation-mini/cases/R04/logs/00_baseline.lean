import Mathlib.Data.Set.Basic
import Mathlib.Util.CountHeartbeats

namespace ValidationMini

theorem r04_inter_union {α : Type*} (s t u : Set α) (x : α) (hx : x ∈ s ∩ (t ∪ u)) :
    x ∈ (s ∩ t) ∪ (s ∩ u) := by
  obtain ⟨hs, htu⟩ := hx
  rcases htu with ht | hu
  · exact Or.inl ⟨hs, ht⟩
  · exact Or.inr ⟨hs, hu⟩

end ValidationMini

#print axioms ValidationMini.r04_inter_union
