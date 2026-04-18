import «keyGet.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct keyGet by
  unfold Pure.keyGet; loom_solve
