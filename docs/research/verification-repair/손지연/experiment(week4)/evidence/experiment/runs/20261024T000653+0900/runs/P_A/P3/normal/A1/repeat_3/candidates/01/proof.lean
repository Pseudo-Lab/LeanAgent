by
  intros Hup Hinit
  have HlenU := UpdateStatesLength Hup
  have HlenI := InitStatesLength Hinit
  have Hdef : isDefined σ ks := UpdateStatesDefined' Hup
  have Hnot : isNotDefined σ ks' :=
    UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
  have Hdis : ks.Disjoint ks' := by
    intro k hk hk'
    have Hsome := Hdef k hk
    have Hnone := Hnot k hk'
    simp [Option.isSome, Hnone] at Hsome
  have Hcomm :
      updatedStates (updatedStates σ ks vs) ks' vs' =
      updatedStates (updatedStates σ ks' vs') ks vs := by
    simp only [updatedStates]
    apply updatedStatesComm
    rw [List.unzip_zip, List.unzip_zip] <;> assumption
  refine ⟨updatedStates σ ks' vs', rfl, ?_, ?_⟩
  · exact updatedStatesInit HlenI Hnot (InitStatesNodup Hinit)
  · rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, Hcomm]
    exact updatedStatesUpdate HlenU (updatedStatesDefMonotone Hdef)