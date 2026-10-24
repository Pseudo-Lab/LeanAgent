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
      (ks'.zip vs').unzip.1.Disjoint (ks.zip vs).unzip.1 := by
    rw [List.unzip_zip] <;> simp_all
  refine ⟨updatedStates σ ks' vs', rfl,
    updatedStatesInit HlenI Hndef (InitStatesNodup Hinit), ?_⟩
  have Hdef₁ : isDefined (updatedStates σ ks' vs') ks :=
    updatedStatesDefMonotone Hdef
  have Heq : updatedStates (updatedStates σ ks' vs') ks vs = σ'' := by
    calc
      updatedStates (updatedStates σ ks' vs') ks vs =
          updatedStates' (updatedStates' σ (ks'.zip vs')) (ks.zip vs) := rfl
      _ = updatedStates' (updatedStates' σ (ks.zip vs)) (ks'.zip vs') :=
        updatedStatesComm Hzip
      _ = updatedStates (updatedStates σ ks vs) ks' vs' := rfl
      _ = updatedStates σ' ks' vs' := by
        rw [← UpdateStatesUpdated Hup]
      _ = σ'' := (InitStatesUpdated Hinit).symm
  exact Heq ▸ updatedStatesUpdate HlenU Hdef₁