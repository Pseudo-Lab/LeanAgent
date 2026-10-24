by
  intro a b c hab hac
  induction hab generalizing c with
  | refl =>
      exact ⟨c, hac, .refl c⟩
  | red_I =>
      cases hac with
      | refl =>
          exact ⟨_, .refl _, .red_I _⟩
      | red_I =>
          exact ⟨_, .refl _, .refl _⟩
      | par hi ha =>
          rw [I_irreducible _ hi]
          exact ⟨_, ha, .red_I _⟩
  | red_K _ =>
      cases hac with
      | refl =>
          exact ⟨_, .refl _, .red_K _ _⟩
      | red_K =>
          exact ⟨_, .refl _, .refl _⟩
      | par hk hb =>
          obtain ⟨x, hx, hk'⟩ := Ka_irreducible _ _ hk
          rw [hk']
          exact ⟨x, hx, .red_K x _⟩
  | red_S _ _ _ =>
      cases hac with
      | refl =>
          exact ⟨_, .refl _, .red_S _ _ _⟩
      | red_S =>
          exact ⟨_, .refl _, .refl _⟩
      | par hs hc =>
          obtain ⟨x, y, hx, hy, hs'⟩ := Sab_irreducible _ _ _ hs
          rw [hs']
          exact
            ⟨x ⬝ _ ⬝ (y ⬝ _),
              .par (.par hx hc) (.par hy hc),
              .red_S x y _⟩
  | par ha hb iha ihb =>
      cases hac with
      | refl =>
          exact ⟨_, .refl _, .par ha hb⟩
      | red_I =>
          rw [I_irreducible _ ha]
          exact ⟨_, .red_I _, hb⟩
      | red_K =>
          obtain ⟨x, hx, ha'⟩ := Ka_irreducible _ _ ha
          rw [ha']
          exact ⟨x, .red_K x _, hx⟩
      | red_S _ _ =>
          obtain ⟨x, y, hx, hy, ha'⟩ := Sab_irreducible _ _ _ ha
          rw [ha']
          exact
            ⟨x ⬝ _ ⬝ (y ⬝ _),
              .red_S x y _,
              .par (.par hx hb) (.par hy hb)⟩
      | par hc hd =>
          obtain ⟨x, hx₁, hx₂⟩ := iha hc
          obtain ⟨y, hy₁, hy₂⟩ := ihb hd
          exact ⟨x ⬝ y, .par hx₁ hy₁, .par hx₂ hy₂⟩