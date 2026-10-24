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
  have Hunzip_fst :
      ∀ (as : List P.Ident) (bs : List P.Expr),
        as.length = bs.length → (as.zip bs).unzip.1 = as := by
    intro as
    induction as with
    | nil =>
      intro bs Hlen
      cases bs <;> simp_all
    | cons a as ih =>
      intro bs Hlen
      cases bs with
      | nil => simp_all
      | cons b bs =>
        simp at Hlen
        simp [ih bs Hlen]
  have Hzipdisj :
      List.Disjoint ((ks'.zip vs').unzip.1) ((ks.zip vs).unzip.1) := by
    rw [Hunzip_fst ks' vs' Hlen', Hunzip_fst ks vs Hlen]
    exact List.Disjoint.symm Hdisj
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