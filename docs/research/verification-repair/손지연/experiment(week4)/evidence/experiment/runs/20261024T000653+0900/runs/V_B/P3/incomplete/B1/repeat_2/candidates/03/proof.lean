by
  intros Hup Hinit
  have Hlen : ks.length = vs.length := UpdateStatesLength Hup
  have Hlen' : ks'.length = vs'.length := InitStatesLength Hinit
  have Hdef : isDefined σ ks := UpdateStatesDefined' Hup
  have Hndef : isNotDefined σ ks' :=
    UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
  have Hnd : ks'.Nodup := InitStatesNodup Hinit
  have Hdisj : ks.Disjoint ks' := by
    intro k Hk Hk'
    have Hsome := Hdef k Hk
    have Hnone := Hndef k Hk'
    simp [Hnone] at Hsome
  have Hinit₁ :
      InitStates σ ks' vs' (updatedStates σ ks' vs') :=
    updatedStatesInit Hlen' Hndef Hnd
  have Hdef₁ : isDefined (updatedStates σ ks' vs') ks := by
    exact updatedStatesDefMonotone Hdef
  have Hup₁ :
      UpdateStates (updatedStates σ ks' vs') ks vs
        (updatedStates (updatedStates σ ks' vs') ks vs) :=
    updatedStatesUpdate Hlen Hdef₁
  have Hzipdisj :
      List.Disjoint ((ks'.zip vs').unzip.1) ((ks.zip vs).unzip.1) := by
    intro k Hk' Hk
    have Hmem' : k ∈ ks' := by
      simp only [List.mem_map] at Hk'
      obtain ⟨p, Hp, rfl⟩ := Hk'
      exact (List.of_mem_zip Hp).1
    have Hmem : k ∈ ks := by
      simp only [List.mem_map] at Hk
      obtain ⟨p, Hp, rfl⟩ := Hk
      exact (List.of_mem_zip Hp).1
    exact Hdisj Hmem Hmem'
  have Hcomm :
      updatedStates (updatedStates σ ks' vs') ks vs =
        updatedStates (updatedStates σ ks vs) ks' vs' := by
    unfold updatedStates
    exact updatedStatesComm Hzipdisj
  have Hfinal :
      updatedStates (updatedStates σ ks' vs') ks vs = σ'' := by
    calc
      updatedStates (updatedStates σ ks' vs') ks vs =
          updatedStates (updatedStates σ ks vs) ks' vs' := Hcomm
      _ = updatedStates σ' ks' vs' := by
        rw [UpdateStatesUpdated Hup]
      _ = σ'' := (InitStatesUpdated Hinit).symm
  rw [Hfinal] at Hup₁
  exact ⟨updatedStates σ ks' vs', rfl, Hinit₁, Hup₁⟩