by
  induction der <;>
    grind [cases Term.Value, cases Red, Sub.refl, Typing.abs_inv,
      Typing.tabs_inv, Typing.inl_inv, Typing.inr_inv]