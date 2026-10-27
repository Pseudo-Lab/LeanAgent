by
  intros Hup Hinit
  have HlenI := InitStatesLength Hinit
  have HlenU := UpdateStatesLength Hup
  have Hndef := InitStatesNotDefined Hinit
  have Hinit₁ : InitStates σ ks' vs' (updatedStates σ ks' vs') :=
    updatedStatesInit HlenI
      (UpdateStatesNotDefMonotone' Hndef Hup)
      (InitStatesNodup Hinit)
  refine ⟨updatedStates σ ks' vs', rfl, Hinit₁, ?_⟩
  have Hdisj : ks'.Disjoint ks := by
    intro k hk' hk
    have hn := Hndef k hk'
    have hd := (UpdateStatesDefined Hup) k hk
    simpa [hn] using hd
  have Hcomm :
      updatedStates (updatedStates σ ks' vs') ks vs =
      updatedStates (updatedStates σ ks vs) ks' vs' := by
    unfold updatedStates
    apply updatedStatesComm
    simpa [List.unzip_zip, HlenI, HlenU] using Hdisj
  rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, ← Hcomm]
  exact updatedStatesUpdate HlenU
    (updatedStatesDefMonotone (UpdateStatesDefined' Hup))