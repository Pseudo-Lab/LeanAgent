by
  intros Hup Hinit
  have hlenI := InitStatesLength Hinit
  have hlenU := UpdateStatesLength Hup
  have hdef := UpdateStatesDefined' Hup
  have hndef : isNotDefined σ ks' :=
    UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
  refine ⟨updatedStates σ ks' vs', rfl,
    updatedStatesInit hlenI hndef (InitStatesNodup Hinit), ?_⟩
  have hdis : ks.Disjoint ks' := by
    intro k hk hk'
    have hkdef := hdef k hk
    have hkundef := hndef k hk'
    simp [hkundef] at hkdef
  have hdis' : ks'.Disjoint ks := hdis.symm
  have hcomm :
      updatedStates (updatedStates σ ks' vs') ks vs =
        updatedStates (updatedStates σ ks vs) ks' vs' := by
    simp only [updatedStates]
    apply updatedStatesComm
    rw [List.unzip_zip, List.unzip_zip] <;> simp_all
  rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, ← hcomm]
  apply updatedStatesUpdate hlenU
  exact updatedStatesDefMonotone hdef