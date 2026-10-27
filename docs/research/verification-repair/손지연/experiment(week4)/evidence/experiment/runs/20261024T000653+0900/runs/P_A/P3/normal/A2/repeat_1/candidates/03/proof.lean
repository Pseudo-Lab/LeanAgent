by
  intro Hup Hinit
  have Hdisj : ks.Disjoint ks' := by
    intro k hk hk'
    have Hdef := UpdateStatesDefined Hup k hk
    simp [Option.isSome, InitStatesNotDefined Hinit k hk'] at Hdef
  refine ⟨_, rfl, updatedStatesInit (InitStatesLength Hinit)
    (UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup)
    (InitStatesNodup Hinit), ?_⟩
  have Hcomm :
      updatedStates (updatedStates σ ks vs) ks' vs' =
        updatedStates (updatedStates σ ks' vs') ks vs := by
    apply updatedStatesComm
    rw [List.unzip_zip (UpdateStatesLength Hup),
      List.unzip_zip (InitStatesLength Hinit)]
    exact Hdisj
  rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, Hcomm]
  exact updatedStatesUpdate (UpdateStatesLength Hup)
    (updatedStatesDefMonotone (UpdateStatesDefined' Hup))