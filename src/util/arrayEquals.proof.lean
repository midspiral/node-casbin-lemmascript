import «arrayEquals.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct arrayEquals by
  loom_solve
