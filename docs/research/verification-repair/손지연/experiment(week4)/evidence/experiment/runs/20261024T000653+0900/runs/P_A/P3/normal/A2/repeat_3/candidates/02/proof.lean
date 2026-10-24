by
  intros Hup Hinit
  have HlenI := InitStatesLength Hinit
  have HlenU := UpdateStatesLength Hup
  have Hndef : isNotDefined σ ks' :=
    UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
  have Hdef : isDefined σ ks := UpdateStatesDefined' Hup
  have Hdisj : ks'.Disjoint ks := by
    intro k hk' hk
    have hd := Hdef k hk
    simp [Hndef k hk'] at hd
  have Hzip :
      ((ks'.zip vs').unzip.1).Disjoint ((ks.zip vs).unzip.1) := by
    rw [List.unzip_zip] <;> simp_all
  refine ⟨_, rfl, updatedStatesInit HlenI Hndef (InitStatesNodup Hinit), ?_⟩
  have Hcomm :
      updatedStates (updatedStates σ ks' vs') ks vs =
      updatedStates (updatedStates σ ks vs) ks' vs' := by
    change updatedStates' (updatedStates' σ (ks'.zip vs')) (ks.zip vs) =
      updatedStates' (updatedStates' σ (ks.zip vs)) (ks'.zip vs')
    exact updatedStatesComm Hzip
  rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, ← Hcomm]
  exact updatedStatesUpdate HlenU (updatedStatesDefMonotone Hdef)