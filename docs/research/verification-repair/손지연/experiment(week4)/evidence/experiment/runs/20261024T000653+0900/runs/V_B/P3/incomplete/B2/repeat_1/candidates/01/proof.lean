by
  intros Hup Hinit
  have Hlen : ks.length = vs.length := UpdateStatesLength Hup
  have Hlen' : ks'.length = vs'.length := InitStatesLength Hinit
  have Hnot' : isNotDefined σ' ks' := InitStatesNotDefined Hinit
  have Hnot : isNotDefined σ ks' :=
    UpdateStatesNotDefMonotone' Hnot' Hup
  have Hnd : ks'.Nodup := InitStatesNodup Hinit
  have Hdef : isDefined σ ks := UpdateStatesDefined' Hup
  have Hdisj : ks.Disjoint ks' := by
    intro k Hk Hk'
    have Hd := Hdef k Hk
    have Hn := Hnot k Hk'
    simp [Hn] at Hd
  have HzipSubset : ∀ (as : List P.Ident) (bs : List P.Expr),
      ∀ {x : P.Ident}, x ∈ (as.zip bs).unzip.1 → x ∈ as := by
    intro as
    induction as with
    | nil =>
      intro bs x Hx
      simp at Hx
    | cons a as ih =>
      intro bs x Hx
      cases bs with
      | nil => simp at Hx
      | cons b bs =>
        simp at Hx
        rcases Hx with Hx | Hx
        · simp_all
        · exact List.mem_cons_of_mem a (ih bs Hx)
  have Hzipdisj :
      (ks.zip vs).unzip.1.Disjoint (ks'.zip vs').unzip.1 := by
    intro k Hk Hk'
    exact Hdisj (HzipSubset ks vs Hk) (HzipSubset ks' vs' Hk')
  have Hcomm :
      updatedStates (updatedStates σ ks vs) ks' vs' =
        updatedStates (updatedStates σ ks' vs') ks vs := by
    unfold updatedStates
    exact updatedStatesComm Hzipdisj
  have Hend :
      updatedStates (updatedStates σ ks' vs') ks vs = σ'' := by
    rw [← Hcomm]
    rw [← UpdateStatesUpdated Hup]
    exact (InitStatesUpdated Hinit).symm
  exists updatedStates σ ks' vs'
  refine ⟨rfl, updatedStatesInit Hlen' Hnot Hnd, ?_⟩
  have Hdef' : isDefined (updatedStates σ ks' vs') ks := by
    apply updatedStatesDefMonotone Hdef
  rw [← Hend]
  exact updatedStatesUpdate Hlen Hdef'