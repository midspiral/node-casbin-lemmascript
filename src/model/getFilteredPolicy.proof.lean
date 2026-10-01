import «getFilteredPolicy.def»

set_option velvet.semantics.termination "total"

prove_correct ruleMatches by
  velvet_vcgen [ruleMatches] with try finish
