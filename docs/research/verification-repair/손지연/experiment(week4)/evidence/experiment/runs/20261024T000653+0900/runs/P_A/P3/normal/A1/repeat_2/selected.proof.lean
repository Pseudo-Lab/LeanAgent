by
  intros Hup Hinit
  have hli := InitStatesLength Hinit
  have hlu := UpdateStatesLength Hup
  refine ⟨updatedStates σ ks' vs', rfl, ?_, ?_⟩
  · exact updatedStatesInit hli
      (UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup)
      (InitStatesNodup Hinit)
  · have hdis : ks'.Disjoint ks := by
      intro k hk' hk
      have hn := (InitStatesNotDefined Hinit) k hk'
      have hd := (UpdateStatesDefined Hup) k hk
      simpa [hn, Option.isSome] using hd
    have hcomm :
        updatedStates (updatedStates σ ks' vs') ks vs =
        updatedStates (updatedStates σ ks vs) ks' vs' := by
      unfold updatedStates
      apply updatedStatesComm
      rw [List.unzip_zip, List.unzip_zip] <;> simp_all
    rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, ← hcomm]
    exact updatedStatesUpdate hlu
      (updatedStatesDefMonotone (UpdateStatesDefined' Hup))