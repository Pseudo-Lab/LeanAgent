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
  have Hcomm :
      updatedStates (updatedStates σ ks' vs') ks vs =
      updatedStates (updatedStates σ ks vs) ks' vs' := by
    unfold updatedStates
    apply updatedStatesComm
    simpa [List.unzip_zip, HlenI, HlenU] using Hdisj
  rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, ← Hcomm]
  exact updatedStatesUpdate HlenU
    (updatedStatesDefMonotone (UpdateStatesDefined' Hup))