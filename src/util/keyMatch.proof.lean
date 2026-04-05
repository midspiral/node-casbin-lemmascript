import «keyMatch.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

section KeyMatchProof
set_option loom.solver "custom"
set_option hygiene false in
macro_rules
| `(tactic|loom_solver) => `(tactic| first
  | grind
  | omega
  | (intro h; subst h; simp_all [JSString.indexOf_lt_length]))
prove_correct keyMatch by
  unfold Pure.keyMatch; loom_solve
end KeyMatchProof
