by
  intros Hup Hinit
  have Hlen : ks.length = vs.length := UpdateStatesLength Hup
  have Hlen' : ks'.length = vs'.length := InitStatesLength Hinit
  have Hnotdef : isNotDefined σ ks' :=
    UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
  have Hnodup : ks'.Nodup := InitStatesNodup Hinit
  have HinitNew :
      InitStates σ ks' vs' (updatedStates σ ks' vs') :=
    updatedStatesInit Hlen' Hnotdef Hnodup
  have Hdefined : isDefined σ ks := UpdateStatesDefined' Hup
  have HupNew :
      UpdateStates (updatedStates σ ks' vs') ks vs
        (updatedStates (updatedStates σ ks' vs') ks vs) := by
    apply updatedStatesUpdate Hlen
    exact updatedStatesDefMonotone Hdefined
  have Hdisj : ks.Disjoint ks' := by
    intro k Hk Hk'
    have Hd := UpdateStatesDefined Hup
    have Hn := InitStatesNotDefined Hinit
    simp [isDefined] at Hd
    simp [isNotDefined] at Hn
    specialize Hd k Hk
    specialize Hn k Hk'
    simp [Option.isSome, Hn] at Hd
  have Hzip : (ks.zip vs).unzip.1 = ks := by
    induction Hup <;> simp_all
  have Hzip' : (ks'.zip vs').unzip.1 = ks' := by
    induction Hinit <;> simp_all
  have Hdisjzip :
      ((ks.zip vs).unzip.1).Disjoint ((ks'.zip vs').unzip.1) := by
    rw [Hzip, Hzip']
    exact Hdisj
  have Hcomm :
      updatedStates (updatedStates σ ks vs) ks' vs' =
        updatedStates (updatedStates σ ks' vs') ks vs := by
    exact updatedStatesComm Hdisjzip
  have HupEq := UpdateStatesUpdated Hup
  have HinitEq := InitStatesUpdated Hinit
  have Hfinal :
      updatedStates (updatedStates σ ks' vs') ks vs = σ'' := by
    calc
      updatedStates (updatedStates σ ks' vs') ks vs =
          updatedStates (updatedStates σ ks vs) ks' vs' := Hcomm.symm
      _ = updatedStates σ' ks' vs' := by rw [← HupEq]
      _ = σ'' := HinitEq.symm
  refine ⟨updatedStates σ ks' vs', rfl, HinitNew, ?_⟩
  rw [Hfinal] at HupNew
  exact HupNew