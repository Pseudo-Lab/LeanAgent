import Mathlib.Data.Set.Basic
import Mathlib.Util.CountHeartbeats

namespace ValidationMini

open Lean Elab Command in
elab "#vm_count_heartbeats " "in" ppLine cmd:command : command => do
  let start ← IO.getNumHeartbeats
  try
    elabCommand (← `(command| set_option Elab.async false in set_option maxHeartbeats 0 in $cmd))
  finally
    let finish ← IO.getNumHeartbeats
    logInfo m!"VM_HEARTBEATS {(finish - start) / 1000}"

#vm_count_heartbeats in
theorem r04_inter_union {α : Type*} (s t u : Set α) (x : α) (hx : x ∈ s ∩ (t ∪ u)) :
    x ∈ (s ∩ t) ∪ (s ∩ u) := by
  aesop

end ValidationMini
