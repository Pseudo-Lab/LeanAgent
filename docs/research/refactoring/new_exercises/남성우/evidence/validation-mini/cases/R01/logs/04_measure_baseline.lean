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
theorem r01_and_swap (P Q R : Prop) (h : (P ∧ Q) ∧ R) : R ∧ P := by
  constructor
  · exact h.2
  · exact h.1.1

end ValidationMini
