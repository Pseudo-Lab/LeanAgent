by
  intro u i
  have hu := UpdateStatesLength u
  have hi := InitStatesLength i
  have hd : ks.Disjoint ks' := by
    intro k hk hk'
    have h := UpdateStatesDefined u k hk
    have hn := InitStatesNotDefined i k hk'
    simp [Option.isSome, hn] at h
  refine ⟨_, rfl, updatedStatesInit hi
    (UpdateStatesNotDefMonotone' (InitStatesNotDefined i) u)
    (InitStatesNodup i), ?_⟩
  rw [InitStatesUpdated i, UpdateStatesUpdated u]
  simp only [updatedStates]
  rw [updatedStatesComm]
  · exact updatedStatesUpdate hu
      (updatedStatesDefMonotone (UpdateStatesDefined' u))
  · rw [List.unzip_zip, List.unzip_zip] <;> assumption