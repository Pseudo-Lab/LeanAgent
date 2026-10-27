theorem parallelReduction_diamond : Diamond ParallelReduction := by
  have joinI (a d : SKI) (h : ParallelReduction (I ⬝ a) d) :
      Join ParallelReduction a d := by
    cases h
    case refl => exact ⟨a, .refl a, .red_I a⟩
    case red_I => exact ⟨a, .refl a, .refl a⟩
    case par c a' hc ha =>
      rw [I_irreducible c hc]
      exact ⟨a', ha, .red_I a'⟩
  have joinK (a b d : SKI) (h : ParallelReduction (K ⬝ a ⬝ b) d) :
      Join ParallelReduction a d := by
    cases h
    case refl => exact ⟨a, .refl a, .red_K a b⟩
    case red_K => exact ⟨a, .refl a, .refl a⟩
    case par c b' hc hb =>
      obtain ⟨a', ha, he⟩ := Ka_irreducible a c hc
      rw [he]
      exact ⟨a', ha, .red_K a' b'⟩
  have joinS (a b c d : SKI) (h : ParallelReduction (S ⬝ a ⬝ b ⬝ c) d) :
      Join ParallelReduction (a ⬝ c ⬝ (b ⬝ c)) d := by
    cases h
    case refl => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .red_S a b c⟩
    case red_S => exact ⟨a ⬝ c ⬝ (b ⬝ c), .refl _, .refl _⟩
    case par e c' he hc =>
      obtain ⟨a', b', ha, hb, heq⟩ := Sab_irreducible a b e he
      rw [heq]
      exact ⟨a' ⬝ c' ⬝ (b' ⬝ c'),
        .par (.par ha hc) (.par hb hc), .red_S a' b' c'⟩
  intro a a₁ a₂ h₁
  induction h₁ generalizing a₂ <;> intro h₂
  case refl a => exact ⟨a₂, h₂, .refl a₂⟩
  case red_I a => exact joinI a a₂ h₂
  case red_K a b => exact joinK a b a₂ h₂
  case red_S a b c => exact joinS a b c a₂ h₂
  case par a a' b b' ha' hb' iha ihb =>
    cases h₂
    case refl => exact ⟨a' ⬝ b', .refl _, .par ha' hb'⟩
    case par a'' b'' ha'' hb'' =>
      obtain ⟨a₃, ha₁, ha₂⟩ := iha ha''
      obtain ⟨b₃, hb₁, hb₂⟩ := ihb hb''
      exact ⟨a₃ ⬝ b₃, .par ha₁ hb₁, .par ha₂ hb₂⟩
    case red_I => exact symm (joinI _ _ (.par ha' hb'))
    case red_K => exact symm (joinK _ _ _ (.par ha' hb'))
    case red_S => exact symm (joinS _ _ _ _ (.par ha' hb'))
