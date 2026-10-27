by
  intro u i
  have hu := UpdateStatesLength u
  have hi := InitStatesLength i
  have hd : ks.Disjoint ks' := by
    intro k hk hk'
    simpa [Option.isSome, InitStatesNotDefined i k hk'] using
      UpdateStatesDefined u k hk
  refine ⟨_, rfl, updatedStatesInit hi
    (UpdateStatesNotDefMonotone' (InitStatesNotDefined i) u)
    (InitStatesNodup i), ?_⟩
  rw [InitStatesUpdated i, UpdateStatesUpdated u]
  simp only [updatedStates]
  rw [updatedStatesComm]
  · exact updatedStatesUpdate hu
      (updatedStatesDefMonotone (UpdateStatesDefined' u))
  · rw [List.unzip_zip, List.unzip_zip] <;> assumption