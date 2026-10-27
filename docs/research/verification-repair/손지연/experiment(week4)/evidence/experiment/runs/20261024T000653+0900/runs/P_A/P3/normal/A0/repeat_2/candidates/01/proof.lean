by
  intros Hup Hinit
  have Hleni := InitStatesLength Hinit
  have Hlenu := UpdateStatesLength Hup
  have Hnew : InitStates σ ks' vs' (updatedStates σ ks' vs') :=
    updatedStatesInit Hleni
      (UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup)
      (InitStatesNodup Hinit)
  refine ⟨updatedStates σ ks' vs', rfl, Hnew, ?_⟩
  have Hdisj : ks.Disjoint ks' := by
    intro k Hk Hk'
    have Hdef := UpdateStatesDefined Hup k Hk
    have Hnot := InitStatesNotDefined Hinit k Hk'
    simpa [Hnot] using Hdef
  have Hcomm :
      updatedStates (updatedStates σ ks vs) ks' vs' =
        updatedStates (updatedStates σ ks' vs') ks vs := by
    simpa [updatedStates] using
      (updatedStatesComm (σ := σ) (kvs := ks.zip vs)
        (kvs' := ks'.zip vs')
        (by simpa [List.unzip_zip, Hlenu, Hleni] using Hdisj))
  have Hend : updatedStates (updatedStates σ ks' vs') ks vs = σ'' := by
    rw [← Hcomm, ← UpdateStatesUpdated Hup, ← InitStatesUpdated Hinit]
  rw [← Hend]
  exact updatedStatesUpdate Hlenu
    (updatedStatesDefMonotone (UpdateStatesDefined' Hup))