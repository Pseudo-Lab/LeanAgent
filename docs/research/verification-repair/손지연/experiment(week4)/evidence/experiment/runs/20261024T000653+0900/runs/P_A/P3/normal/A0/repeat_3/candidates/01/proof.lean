by
  intros Hup Hinit
  refine ⟨updatedStates σ ks' vs', rfl, ?_, ?_⟩
  · apply updatedStatesInit (InitStatesLength Hinit)
    · exact UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
    · exact InitStatesNodup Hinit
  · have Hdis : ks'.Disjoint ks := by
      intro k hk' hk
      have Hnone := (InitStatesNotDefined Hinit) k hk'
      have Hsome := (UpdateStatesDefined Hup) k hk
      simp [Option.isSome, Hnone] at Hsome
    have Hcomm :
        updatedStates (updatedStates σ ks' vs') ks vs =
          updatedStates (updatedStates σ ks vs) ks' vs' := by
      simp only [updatedStates]
      apply updatedStatesComm
      rw [List.unzip_zip, List.unzip_zip] <;> simp_all [InitStatesLength Hinit, UpdateStatesLength Hup]
    rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, ← Hcomm]
    apply updatedStatesUpdate (UpdateStatesLength Hup)
    apply updatedStatesDefMonotone
    exact UpdateStatesDefined' Hup