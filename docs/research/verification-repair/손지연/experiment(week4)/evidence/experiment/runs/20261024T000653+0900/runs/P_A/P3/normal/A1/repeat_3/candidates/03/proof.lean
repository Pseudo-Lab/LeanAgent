by
  intros Hup Hinit
  have HlenI := InitStatesLength Hinit
  have HlenU := UpdateStatesLength Hup
  have Hdisj : ks'.Disjoint ks := by
    intro k hk' hk
    have hn : σ' k = none := (InitStatesNotDefined Hinit) k hk'
    have hd : (σ' k).isSome = true := (UpdateStatesDefined Hup) k hk
    simp [hn] at hd
  have Hcomm :
      updatedStates (updatedStates σ ks' vs') ks vs =
        updatedStates (updatedStates σ ks vs) ks' vs' := by
    simp only [updatedStates]
    apply updatedStatesComm
    rw [List.unzip_zip, List.unzip_zip] <;> simp_all
  refine ⟨updatedStates σ ks' vs', rfl, ?_, ?_⟩
  · apply updatedStatesInit HlenI
    · exact UpdateStatesNotDefMonotone'
        (InitStatesNotDefined Hinit) Hup
    · exact InitStatesNodup Hinit
  · have Hu := updatedStatesUpdate HlenU
      (updatedStatesDefMonotone (UpdateStatesDefined' Hup) :
        isDefined (updatedStates σ ks' vs') ks)
    rw [Hcomm, ← UpdateStatesUpdated Hup, ← InitStatesUpdated Hinit] at Hu
    exact Hu