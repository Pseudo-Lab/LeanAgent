by
  intros Hup Hinit
  have HlenI := InitStatesLength Hinit
  have HlenU := UpdateStatesLength Hup
  have Hdisj : ks.Disjoint ks' := by
    intro k Hk Hk'
    have Hd := (UpdateStatesDefined Hup) k Hk
    have Hn := (InitStatesNotDefined Hinit) k Hk'
    simpa [Option.isSome, Hn] using Hd
  refine ⟨updatedStates σ ks' vs', rfl, ?_, ?_⟩
  · exact updatedStatesInit HlenI
      (UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup)
      (InitStatesNodup Hinit)
  · have Hcomm :
        updatedStates (updatedStates σ ks vs) ks' vs' =
          updatedStates (updatedStates σ ks' vs') ks vs := by
      unfold updatedStates
      apply updatedStatesComm
      simpa [List.unzip_zip, HlenU, HlenI] using Hdisj
    have Heq :
        σ'' = updatedStates (updatedStates σ ks' vs') ks vs := by
      calc
        σ'' = updatedStates σ' ks' vs' := InitStatesUpdated Hinit
        _ = updatedStates (updatedStates σ ks vs) ks' vs' := by
          rw [UpdateStatesUpdated Hup]
        _ = updatedStates (updatedStates σ ks' vs') ks vs := Hcomm
    rw [Heq]
    apply updatedStatesUpdate HlenU
    exact updatedStatesDefMonotone (UpdateStatesDefined' Hup)