by
  intro u i
  have li := InitStatesLength i
  have lu := UpdateStatesLength u
  have n := UpdateStatesNotDefMonotone' (InitStatesNotDefined i) u
  have d : ks.Disjoint ks' := by
    intro k hk hk'
    simpa [n k hk'] using (UpdateStatesDefined' u) k hk
  have c :
      updatedStates (updatedStates σ ks vs) ks' vs' =
        updatedStates (updatedStates σ ks' vs') ks vs := by
    simp only [updatedStates]
    apply updatedStatesComm
    simpa only [List.unzip_zip lu, List.unzip_zip li] using d
  refine ⟨_, rfl, updatedStatesInit li n (InitStatesNodup i), ?_⟩
  rw [InitStatesUpdated i, UpdateStatesUpdated u, c]
  exact updatedStatesUpdate lu
    (updatedStatesDefMonotone (UpdateStatesDefined' u))