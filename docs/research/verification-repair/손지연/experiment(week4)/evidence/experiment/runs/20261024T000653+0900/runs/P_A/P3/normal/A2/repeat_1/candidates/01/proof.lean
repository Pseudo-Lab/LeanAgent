by
  intro Hup Hinit
  refine ⟨_, rfl, ?_, ?_⟩
  · exact updatedStatesInit (InitStatesLength Hinit)
      (UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup)
      (InitStatesNodup Hinit)
  · have Hdisj : ks.Disjoint ks' := by
      intro k hk hk'
      have hd := UpdateStatesDefined Hup k hk
      have hn := InitStatesNotDefined Hinit k hk'
      simp [Option.isSome, hn] at hd
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