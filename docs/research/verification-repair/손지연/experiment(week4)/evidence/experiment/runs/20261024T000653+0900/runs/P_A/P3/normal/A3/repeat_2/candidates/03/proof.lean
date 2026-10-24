by
  intros Hup Hinit
  have HlenI := InitStatesLength Hinit
  have HlenU := UpdateStatesLength Hup
  have Hndef := InitStatesNotDefined Hinit
  have Hdisj : ks'.Disjoint ks := by
    intro k hk' hk
    have hd := (UpdateStatesDefined Hup) k hk
    simp [Hndef k hk'] at hd
  refine ⟨_, rfl, updatedStatesInit HlenI
    (UpdateStatesNotDefMonotone' Hndef Hup) (InitStatesNodup Hinit), ?_⟩
  rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup]
  unfold updatedStates
  rw [← updatedStatesComm]
  · exact updatedStatesUpdate HlenU
      (updatedStatesDefMonotone (UpdateStatesDefined' Hup))
  · simpa [List.unzip_zip, HlenI, HlenU] using Hdisj