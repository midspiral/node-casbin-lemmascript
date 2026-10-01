import «arrayEquals.def»

set_option velvet.semantics.termination "total"

prove_correct arrayEquals by
  velvet_vcgen [arrayEquals] with try finish
