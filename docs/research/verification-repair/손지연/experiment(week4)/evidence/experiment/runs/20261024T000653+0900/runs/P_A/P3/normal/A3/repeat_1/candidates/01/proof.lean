by
  intros Hup Hinit
  have hli := InitStatesLength Hinit
  have hlu := UpdateStatesLength Hup
  have hni := InitStatesNotDefined Hinit
  have hn := UpdateStatesNotDefMonotone' hni Hup
  have hd : ks.Disjoint ks' := by
    intro k hk hk'
    have h₁ := (UpdateStatesDefined' Hup) k hk
    have h₂ := hn k hk'
    simp [h₂] at h₁
  have hc :
      updatedStates (updatedStates σ ks vs) ks' vs' =
        updatedStates (updatedStates σ ks' vs') ks vs := by
    simp only [updatedStates]
    apply updatedStatesComm
    rw [List.unzip_zip, List.unzip_zip] <;> simp_all
  refine ⟨_, rfl, updatedStatesInit hli hn (InitStatesNodup Hinit), ?_⟩
  rw [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, hc]
  exact updatedStatesUpdate hlu
    (updatedStatesDefMonotone (UpdateStatesDefined' Hup))