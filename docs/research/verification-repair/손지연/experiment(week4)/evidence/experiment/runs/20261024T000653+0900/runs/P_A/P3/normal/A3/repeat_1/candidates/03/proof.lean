by
  intro u i
  have lu := UpdateStatesLength u
  have li := InitStatesLength i
  have n := UpdateStatesNotDefMonotone' (InitStatesNotDefined i) u
  have d : ks.Disjoint ks' := by
    intro k hk hk'
    simpa [n k hk'] using (UpdateStatesDefined' u) k hk
  refine ⟨_, rfl, updatedStatesInit li n (InitStatesNodup i), ?_⟩
  rw [InitStatesUpdated i, UpdateStatesUpdated u]
  unfold updatedStates
  rw [updatedStatesComm (by
    simpa only [List.unzip_zip lu, List.unzip_zip li] using d)]
  exact updatedStatesUpdate lu
    (updatedStatesDefMonotone (UpdateStatesDefined' u))