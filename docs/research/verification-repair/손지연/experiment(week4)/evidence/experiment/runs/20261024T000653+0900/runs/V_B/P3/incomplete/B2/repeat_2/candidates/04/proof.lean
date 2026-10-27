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
  have Hdef' : isDefined (updatedStates σ ks' vs') ks := by
    simpa [updatedStates] using
      (updatedStatesDefMonotone (ves := ks'.zip vs') Hdef)
  have Hup' :
      UpdateStates (updatedStates σ ks' vs') ks vs
        (updatedStates (updatedStates σ ks' vs') ks vs) :=
    updatedStatesUpdate Hlen Hdef'
  have zip_fst :
      ∀ (as : List P.Ident) (bs : List P.Expr),
        as.length = bs.length →
        List.map Prod.fst (as.zip bs) = as := by
    intro as
    induction as with
    | nil =>
      intro bs _
      simp
    | cons a as ih =>
      intro bs H
      cases bs with
      | nil => simp at H
      | cons b bs =>
        simp at H
        simp [ih bs H]
  have Hzipdisj :
      List.Disjoint (ks.zip vs).unzip.1 (ks'.zip vs').unzip.1 := by
    change List.Disjoint (List.map Prod.fst (ks.zip vs))
      (List.map Prod.fst (ks'.zip vs'))
    rw [zip_fst ks vs Hlen, zip_fst ks' vs' Hlen']
    exact Hdisj
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