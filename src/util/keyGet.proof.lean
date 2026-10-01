import «keyGet.def»

set_option velvet.semantics.termination "total"

prove_correct keyGet by
  velvet_vcgen [keyGet] with finish [Pure.keyGet]
