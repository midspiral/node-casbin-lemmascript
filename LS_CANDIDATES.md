# LemmaScript Verification Candidates

## Verified

### Lean (per-step + sequence-level)

- **`pushEffectStep`** (`src/effect/effectorPure.ts:15`) — 8 ensures, 10 Hoare triples, pure function
- **`processEffects`** (`src/effect/effectorPure.ts:50`) — loop with mode-specific invariants, custom solver
- **`arrayEquals`** (`src/util/arrayEquals.ts`) — loop with break, 3 ensures, `loom_solve` fully automatic
- **`keyMatch`** (`src/util/keyMatch.ts`) — string methods (indexOf, slice), custom solver for unreachable branch
- **`keyGet`** (`src/util/keyGet.ts`) — extracts matched substring from wildcard, wired into casbin
- **`ruleMatches`** (`src/model/getFilteredPolicy.ts`) — field-level policy matching with loop invariants

### Dafny (39 lemmas in `effectorPure.proofs.dfy`)

- End-to-end correctness for all 4 modes (AllowSome, DenyNone, AllowAndDeny, Priority)
- Order independence: swapping adjacent effects doesn't change the decision
- Per-step properties, stability invariants

## Tier 1 — Pure, no blockers

- **`array2DEquals`** (`src/util/util.ts:57`) — delegates to `arrayEquals`. Typo on line 59: `bLen = a.length` instead of `b.length` (harmless if callers always pass same-length arrays).

## Tier 2 — Interesting logic, minor work

- **`filterPolicies`** (`src/model/getFilteredPolicy.ts`) — Dafny spec generated, `ruleMatches` verified. Outer loop over policies not yet proved in Lean.
- **`removeFilteredPolicy`** (`src/model/model.ts:401`) — partitions policies into kept/removed. Prove no rules lost.
- **`Role.hasRole`** (`src/rbac/defaultRoleManager.ts:57`) — recursive RBAC hierarchy check with bounded depth. Needs recursion support in LemmaScript.

## Tier 3 — Partial extraction needed

- **`keyMatch2`** (`src/util/builtinOperators.ts:77`) — pattern transformation loop is pure; regex validation at end is trust boundary.
- **`keyMatch3`** (`src/util/builtinOperators.ts:135`) — same shape as keyMatch2, `{param}` syntax.

## Out of scope (unsupported features)

- `escapeAssertion` — regex callback
- `arrayRemoveDuplicates` — `new Set()`
- `keyMatch4` — Map + regex
- `ip.*` — Buffer, forEach callbacks
- `generateGFunction` — closures
