by
  intros Hup Hinit
  have HlenU := UpdateStatesLength Hup
  have HlenI := InitStatesLength Hinit
  have Hinit' : InitStates σ ks' vs' (updatedStates σ ks' vs') :=
    updatedStatesInit HlenI
      (UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup)
      (InitStatesNodup Hinit)
  refine ⟨_, rfl, Hinit', ?_⟩
  have Hdis : ks.Disjoint ks' := by
    intro k hk hk'
    have Hd := UpdateStatesDefined Hup k hk
    have Hn := InitStatesNotDefined Hinit k hk'
    rw [Hn] at Hd
    simp [Option.isSome] at Hd
  have Hzip :
      (ks'.zip vs').unzip.1.Disjoint (ks.zip vs).unzip.1 := by
    simpa [List.unzip_zip, HlenI, HlenU] using Hdis.symm
  have Hcomm :
      updatedStates (updatedStates σ ks' vs') ks vs =
        updatedStates (updatedStates σ ks vs) ks' vs' := by
    simpa [updatedStates] using
      (updatedStatesComm (σ := σ) (kvs := ks'.zip vs')
        (kvs' := ks.zip vs) Hzip)
  have Hend :
      updatedStates (updatedStates σ ks' vs') ks vs = σ'' := by
    rw [Hcomm, ← UpdateStatesUpdated Hup, ← InitStatesUpdated Hinit]
  have Hdef : isDefined (updatedStates σ ks' vs') ks := by
    simpa [updatedStates] using
      (updatedStatesDefMonotone (ves := ks'.zip vs')
        (UpdateStatesDefined' Hup))
  rw [← Hend]
  exact updatedStatesUpdate HlenU Hdef