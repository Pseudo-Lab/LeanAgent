by
  intros Hup Hinit
  have Hlen := InitStatesLength Hinit
  have Hndef :=
    UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
  have Hinit' :=
    updatedStatesInit Hlen Hndef (InitStatesNodup Hinit)
  refine ⟨_, rfl, Hinit', ?_⟩
  have Hlen' := UpdateStatesLength Hup
  have Hdisj : ks.Disjoint ks' := by
    intro k hk hk'
    have Hd := (UpdateStatesDefined' Hup) k hk
    have Hn := Hndef k hk'
    simp [Option.isSome, Hn] at Hd
  have Hzip :
      (ks.zip vs).unzip.1.Disjoint (ks'.zip vs').unzip.1 := by
    rw [List.unzip_zip, List.unzip_zip] <;> assumption
  have Hcomm :
      updatedStates (updatedStates σ ks vs) ks' vs' =
        updatedStates (updatedStates σ ks' vs') ks vs := by
    simp only [updatedStates]
    exact updatedStatesComm Hzip
  rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, Hcomm]
  exact updatedStatesUpdate Hlen'
    (updatedStatesDefMonotone (UpdateStatesDefined' Hup))