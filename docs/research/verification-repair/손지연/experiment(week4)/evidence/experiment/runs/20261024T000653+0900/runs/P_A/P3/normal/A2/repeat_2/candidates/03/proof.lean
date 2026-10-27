by
  intros Hup Hinit
  have Hlen := UpdateStatesLength Hup
  have Hlen' := InitStatesLength Hinit
  have Hdef := UpdateStatesDefined' Hup
  have Hndef := UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
  have Hdisj : ks.Disjoint ks' := by
    intro k hk hk'
    simpa [Hndef k hk', Option.isSome] using Hdef k hk
  refine ⟨_, rfl, updatedStatesInit Hlen' Hndef (InitStatesNodup Hinit), ?_⟩
  have Hcomm :
      updatedStates (updatedStates σ ks vs) ks' vs' =
        updatedStates (updatedStates σ ks' vs') ks vs :=
    updatedStatesComm (by
      simpa [List.unzip_zip Hlen, List.unzip_zip Hlen'] using Hdisj)
  rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, Hcomm]
  exact updatedStatesUpdate Hlen (updatedStatesDefMonotone Hdef)