by
  intros Hup Hinit
  have Hlen := UpdateStatesLength Hup
  have Hlen' := InitStatesLength Hinit
  have Hdis : ks.Disjoint ks' := by
    intro k hk hk'
    have hd := UpdateStatesDefined Hup k hk
    have hn := InitStatesNotDefined Hinit k hk'
    simp [Option.isSome, hn] at hd
  refine ⟨_, rfl, ?_, ?_⟩
  · exact updatedStatesInit Hlen'
      (UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup)
      (InitStatesNodup Hinit)
  · rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup]
    simp only [updatedStates]
    rw [updatedStatesComm]
    · exact updatedStatesUpdate Hlen
        (updatedStatesDefMonotone (UpdateStatesDefined' Hup))
    · rw [List.unzip_zip, List.unzip_zip] <;> assumption