lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  generalize eq : [] = Γ at der
  let lc := der.wf.2.1
  induction der <;> subst eq
  case var mem => simp at mem
  case app l r il ir =>
    right
    rcases il rfl with vl | ⟨t', hl⟩
    · rcases ir rfl with vr | ⟨t', hr⟩
      · obtain ⟨_, _, rfl⟩ := l.canonical_form_abs vl
        exact ⟨_, .abs vl.lc vr⟩
      · exact ⟨_, .appᵣ vl hr⟩
    · exact ⟨_, .appₗ r.wf.2.1 hl⟩
  case tapp der sub ih =>
    right
    rcases ih rfl with v | ⟨t', h⟩
    · obtain ⟨_, _, rfl⟩ := der.canonical_form_tabs v
      exact ⟨_, .tabs v.lc sub.wf.2.1.lc⟩
    · exact ⟨_, .tapp sub.wf.2.1.lc h⟩
  case let' ih _ =>
    right
    have hb := (body_let.mp lc).2
    rcases ih rfl with v | ⟨t', h⟩ <;>
      solve_by_elim [Exists.intro, Red.let_body, Red.let_bind]
  case inl ih | inr ih =>
    rcases ih rfl with v | ⟨_, h⟩ <;>
      solve_by_elim [Or.inl, Or.inr, Exists.intro, Value.inl, Value.inr, Red.inl, Red.inr]
  case case der _ _ ih _ _ =>
    right
    obtain ⟨_, hb₂, hb₃⟩ := body_case.mp lc
    rcases ih rfl with v | ⟨t', h⟩
    · obtain ⟨t', rfl | rfl⟩ := der.canonical_form_sum v
      all_goals cases v
      all_goals apply_rules [Exists.intro, Term.Red.case_inl, Term.Red.case_inr]
    · exact ⟨_, .case h hb₂ hb₃⟩
  all_goals first
  | left; constructor; exact lc
  | rename_i ih; exact ih rfl
