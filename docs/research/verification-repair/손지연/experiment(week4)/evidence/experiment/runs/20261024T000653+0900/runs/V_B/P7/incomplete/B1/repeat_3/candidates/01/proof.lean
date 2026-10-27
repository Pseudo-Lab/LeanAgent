by
  induction der <;>
    grind [cases Value, Sub.refl, Typing.abs_inv, Typing.tabs_inv,
      Typing.inl_inv, Typing.inr_inv]