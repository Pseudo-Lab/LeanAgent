by
  intros Hup Hinit
  have Hleni := InitStatesLength Hinit
  have Hlenu := UpdateStatesLength Hup
  have Hdisj : ks'.Disjoint ks := by
    intro k Hki Hku
    have Hnone := InitStatesNotDefined Hinit k Hki
    have Hsome := UpdateStatesDefined Hup k Hku
    simp [Hnone, Option.isSome] at Hsome
  have Hcomm :
      updatedStates (updatedStates σ ks' vs') ks vs =
        updatedStates (updatedStates σ ks vs) ks' vs' := by
    unfold updatedStates
    apply updatedStatesComm
    rw [List.unzip_zip, List.unzip_zip] <;> simp_all
  refine ⟨updatedStates σ ks' vs', rfl, ?_, ?_⟩
  · exact updatedStatesInit Hleni
      (UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup)
      (InitStatesNodup Hinit)
  · rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, ← Hcomm]
    exact updatedStatesUpdate Hlenu
      (updatedStatesDefMonotone (UpdateStatesDefined' Hup))