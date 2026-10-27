by
  intros Hup Hinit
  have Hlen := UpdateStatesLength Hup
  have Hlen' := InitStatesLength Hinit
  have Hdisj : ks'.Disjoint ks := by
    intro k hk' hk
    have Hnone := (InitStatesNotDefined Hinit) k hk'
    have Hsome := (UpdateStatesDefined Hup) k hk
    simp [Hnone, Option.isSome] at Hsome
  refine ⟨updatedStates σ ks' vs', rfl, ?_, ?_⟩
  · apply updatedStatesInit Hlen'
    · exact UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
    · exact InitStatesNodup Hinit
  · have Hcomm :
        updatedStates (updatedStates σ ks' vs') ks vs =
          updatedStates (updatedStates σ ks vs) ks' vs' := by
      unfold updatedStates
      apply updatedStatesComm
      rw [List.unzip_zip, List.unzip_zip] <;> simp_all
    have Hup' :
        UpdateStates (updatedStates σ ks' vs') ks vs
          (updatedStates (updatedStates σ ks' vs') ks vs) :=
      updatedStatesUpdate Hlen
        (updatedStatesDefMonotone (UpdateStatesDefined' Hup))
    rw [Hcomm, ← UpdateStatesUpdated Hup, ← InitStatesUpdated Hinit] at Hup'
    exact Hup'