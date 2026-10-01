import «keyMatch.def»

set_option velvet.semantics.termination "total"

prove_correct keyMatch by
  velvet_vcgen [keyMatch]
  intro h
  subst h
  simp only [Pure.keyMatch]
  split
  · simp
  · rename_i hpos
    have hbound := JSString.indexOf_lt_length _ _ hpos
    simp [hbound.2]
