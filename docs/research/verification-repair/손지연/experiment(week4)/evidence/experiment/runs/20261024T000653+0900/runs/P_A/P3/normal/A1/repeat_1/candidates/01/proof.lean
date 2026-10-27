by
  intros Hup Hinit
  have HlenU := UpdateStatesLength Hup
  have HlenI := InitStatesLength Hinit
  refine ⟨updatedStates σ ks' vs', rfl, ?_, ?_⟩
  · apply updatedStatesInit HlenI
    · exact UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
    · exact InitStatesNodup Hinit
  · have Hdef : isDefined (updatedStates σ ks' vs') ks := by
      apply updatedStatesDefMonotone
      exact UpdateStatesDefined' Hup
    have Hdis : ks'.Disjoint ks := by
      have Hnot := InitStatesNotDefined Hinit
      have Hyes := UpdateStatesDefined Hup
      simp [isNotDefined] at Hnot
      simp [isDefined] at Hyes
      intro k Hk' Hk
      specialize Hnot k Hk'
      specialize Hyes k Hk
      simp [Hnot] at Hyes
    have Hcomm :
        updatedStates (updatedStates σ ks' vs') ks vs =
          updatedStates (updatedStates σ ks vs) ks' vs' := by
      apply updatedStatesComm
      simpa [List.unzip_zip] using Hdis
    have Hupdate := updatedStatesUpdate HlenU Hdef
    rw [Hcomm, ← UpdateStatesUpdated Hup, ← InitStatesUpdated Hinit] at Hupdate
    exact Hupdate