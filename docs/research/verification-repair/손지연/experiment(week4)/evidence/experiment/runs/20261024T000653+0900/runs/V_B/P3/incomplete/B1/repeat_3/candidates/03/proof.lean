by
  intros Hup Hinit
  have HlenUp : ks.length = vs.length :=
    UpdateStatesLength Hup
  have Hnotdef : isNotDefined σ ks' :=
    UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup
  have Hinit₁ :
      InitStates σ ks' vs' (updatedStates σ ks' vs') :=
    updatedStatesInit (InitStatesLength Hinit) Hnotdef
      (InitStatesNodup Hinit)
  have Hdisj : ks.Disjoint ks' := by
    intro k Hk Hk'
    have Hdefk := (UpdateStatesDefined Hup) k Hk
    have Hnone := (InitStatesNotDefined Hinit) k Hk'
    rw [Hnone] at Hdefk
    simp [Option.isSome] at Hdefk
  have Hdefined : isDefined (updatedStates σ ks' vs') ks := by
    intro k Hk
    have Hkdef := (UpdateStatesDefined' Hup) k Hk
    cases Hsome : σ k with
    | none =>
      simp [Option.isSome, Hsome] at Hkdef
    | some value =>
      have Hpres :
          updatedStates σ ks' vs' k = some value :=
        InitStatesSomeMonotone Hsome Hinit₁
      simp [Option.isSome, Hpres]
  have HmemZip :
      ∀ {as : List P.Ident} {bs : List P.Expr} {x : P.Ident},
        x ∈ (as.zip bs).unzip.1 → x ∈ as := by
    intro as bs x Hmem
    induction as generalizing bs with
    | nil => simp_all
    | cons a as ih =>
      cases bs with
      | nil => simp_all
      | cons b bs =>
        simp at Hmem ⊢
        rcases Hmem with h | ⟨y, hy⟩
        · exact Or.inl h
        · exact Or.inr (List.of_mem_zip hy).1
  have HpairDisj :
      List.Disjoint ((ks'.zip vs').unzip.1) ((ks.zip vs).unzip.1) := by
    intro k Hk' Hk
    exact Hdisj (HmemZip Hk) (HmemZip Hk')
  have Hcomm :
      updatedStates (updatedStates σ ks' vs') ks vs =
        updatedStates (updatedStates σ ks vs) ks' vs' := by
    simpa [updatedStates] using
      (updatedStatesComm (σ := σ)
        (kvs := ks'.zip vs') (kvs' := ks.zip vs) HpairDisj)
  have HupEq : σ' = updatedStates σ ks vs :=
    UpdateStatesUpdated Hup
  have HinitEq : σ'' = updatedStates σ' ks' vs' :=
    InitStatesUpdated Hinit
  have Htarget :
      updatedStates (updatedStates σ ks' vs') ks vs = σ'' := by
    rw [HinitEq, HupEq]
    exact Hcomm
  refine ⟨updatedStates σ ks' vs', rfl, Hinit₁, ?_⟩
  rw [← Htarget]
  exact updatedStatesUpdate HlenUp Hdefined