by
  intros Hup Hinit
  have Hlen := UpdateStatesLength Hup
  have Hlen' := InitStatesLength Hinit
  have Hndef' := InitStatesNotDefined Hinit
  have Hndef : isNotDefined σ ks' :=
    UpdateStatesNotDefMonotone' Hndef' Hup
  have Hnd' := InitStatesNodup Hinit
  have Hdef : isDefined σ ks := UpdateStatesDefined' Hup
  have Hdisj : ks.Disjoint ks' := by
    intros k Hk Hk'
    have Hd := Hdef k Hk
    have Hn := Hndef k Hk'
    rw [Hn] at Hd
    simp at Hd
  have Hinit' :
      InitStates σ ks' vs' (updatedStates σ ks' vs') :=
    updatedStatesInit Hlen' Hndef Hnd'
  have Hdef' : isDefined (updatedStates σ ks' vs') ks :=
    InitStatesDefMonotone Hdef Hinit'
  have Hup' :
      UpdateStates (updatedStates σ ks' vs') ks vs
        (updatedStates (updatedStates σ ks' vs') ks vs) :=
    updatedStatesUpdate Hlen Hdef'
  have Hzipdisj :
      (ks.zip vs).unzip.1.Disjoint (ks'.zip vs').unzip.1 := by
    simpa [Hlen, Hlen'] using Hdisj
  have Hcomm :=
    updatedStatesComm (σ := σ) (kvs := ks.zip vs)
      (kvs' := ks'.zip vs') Hzipdisj
  have Hsame :
      updatedStates (updatedStates σ ks' vs') ks vs = σ'' := by
    have HupEq := UpdateStatesUpdated Hup
    have HinitEq := InitStatesUpdated Hinit
    rw [HinitEq, HupEq]
    simpa [updatedStates] using Hcomm.symm
  refine ⟨updatedStates σ ks' vs', rfl, Hinit', ?_⟩
  rw [← Hsame]
  exact Hup'