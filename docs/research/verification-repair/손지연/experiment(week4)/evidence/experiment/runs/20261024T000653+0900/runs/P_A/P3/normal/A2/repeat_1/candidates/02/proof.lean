by
  intro Hup Hinit
  have Hlen := UpdateStatesLength Hup
  have Hlen' := InitStatesLength Hinit
  have Hndef := InitStatesNotDefined Hinit
  have Hdisj : ks.Disjoint ks' := by
    intro k hk hk'
    have Hdef := UpdateStatesDefined Hup k hk
    have Hnone := Hndef k hk'
    simp [Option.isSome, Hnone] at Hdef
  refine ⟨_, rfl, ?_, ?_⟩
  · exact updatedStatesInit Hlen'
      (UpdateStatesNotDefMonotone' Hndef Hup)
      (InitStatesNodup Hinit)
  · have Hcomm :
        updatedStates (updatedStates σ ks vs) ks' vs' =
          updatedStates (updatedStates σ ks' vs') ks vs := by
      apply updatedStatesComm
      rw [List.unzip_zip Hlen, List.unzip_zip Hlen']
      exact Hdisj
    rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, Hcomm]
    exact updatedStatesUpdate Hlen
      (updatedStatesDefMonotone (UpdateStatesDefined' Hup))