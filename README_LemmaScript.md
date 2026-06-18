# Casbin Effector — Verified with LemmaScript

[![LemmaScript: verified](https://img.shields.io/badge/LemmaScript-verified-brightgreen)](https://github.com/midspiral/node-casbin-lemmascript/actions/workflows/lemmascript.yml)


This is a fork of [apache/casbin-node-casbin](https://github.com/apache/casbin-node-casbin) with formal verification of the Effector module using [LemmaScript](https://github.com/midspiral/LemmaScript). [View as Diff](https://github.com/midspiral/node-casbin-lemmascript/compare/2e66ca9cea3c05aa06775e5d75437724d1ff71f7..HEAD).

The Effector is the security-critical component that combines per-rule Allow/Deny/Indeterminate effects into a single boolean access decision. A bug here means an access bypass. We formally verify it using LemmaScript — annotating the TypeScript directly with specifications and proving correctness in Lean 4.

## Setup

**Prerequisites:** [elan](https://github.com/leanprover/elan) (Lean 4 toolchain), Node.js ≥ 18.

**Clone dependencies:**

```sh
git clone https://github.com/namin/loom.git -b lemma ../loom
git clone https://github.com/namin/velvet.git -b lemma ../velvet
git clone https://github.com/midspiral/LemmaScript.git ../LemmaScript
```

**Install LemmaScript tools:**

```sh
cd ../LemmaScript/tools && npm install
```

**Build (first time fetches mathlib cache, ~5 min):**

```sh
lake build
```

**Run tests (verify the refactored code passes all existing tests):**

```sh
npm install
npx jest --testPathPattern=enforcer
```

All 217 existing tests pass with verified code wired in.

## What's Verified

### Effector — Per-Step Properties

`pushEffectStep` is a pure function extracted from `DefaultEffectorStream.pushEffect`. The class delegates to it. Verified ensures (all proved automatically by `loom_solve`):

- **Done stability:** `state.done ==> \result === state`
- **Allow mode:** `!state.done && mode === "allow" && eft === "allow" ==> \result.res && \result.done`
- **Deny mode:** `!state.done && mode === "deny" && eft === "deny" ==> !\result.res && \result.done`
- **Priority mode:** non-Indeterminate decides; Indeterminate skips

Plus 10 standalone Hoare triples about individual calls.

### Effector — Sequence-Level Properties

End-to-end correctness over full effect sequences, proved by induction in pure Lean:

- **AllowSome correctness:** `foldEffects .allow efts initState).res = true ↔ hasAllow efts` — the result is true if and only if at least one Allow effect exists
- **DenyNone correctness:** `(foldEffects .deny efts initState).res = true ↔ ¬hasDeny efts` — the result is true if and only if no Deny effect exists (for non-empty lists)
- **AllowSome order independence:** swapping any adjacent pair doesn't change the allow-mode result
- **AllowAndDeny order independence:** swapping any adjacent pair doesn't change the allow_and_deny result
- **DenyNone order independence:** swapping any adjacent pair doesn't change the deny result
- **Done stability across sequences:** once done, stays done through any number of effects
- **AllowMode done→res:** in allow mode, done always implies res=true
- **DenyMode done→¬res:** in deny mode, done always implies res=false
- **AllowAndDeny correctness:** `foldEffects .allow_and_deny efts initState).res = true ↔ hasAllow efts ∧ ¬hasDeny efts` — result is true iff at least one Allow AND no Deny
- **Priority correctness:** first non-Indeterminate effect decides: allow→true, deny→false, all indeterminate→false

### Util — Verified and Wired In

- **`keyMatch`** (`src/util/keyMatch.ts`) — wildcard pattern matching with string methods (indexOf, slice). Replaces the original in casbin.
- **`keyGet`** (`src/util/keyGet.ts`) — extracts the matched part after a wildcard. 3 ensures: no wildcard → empty, key too short → empty, prefix mismatch → empty.
- **`arrayEquals`** (`src/util/arrayEquals.ts`) — loop with break, 3 ensures, fully automatic.

## File Structure

```
src/effect/
  effectorPure.ts              ← Annotated TypeScript (pure function + processEffects)
  effectorPure.types.lean      ← Generated: Mode, Eft, EffectState types
  effectorPure.spec.lean       ← Pure Lean mirror (stepPure, foldEffects, hasAllow, hasDeny)
  effectorPure.def.lean        ← Generated: Velvet method definitions
  effectorPure.proof.lean      ← All proofs: per-step + sequence-level
  effectorPure.dfy             ← Generated: Dafny specification
  effectorPure.proofs.dfy      ← Dafny proofs: correctness + order independence (39 verified)
  defaultEffectorStream.ts     ← Original class, refactored to delegate to effectorPure
```

### Dafny Proofs

The same spec is also verified in Dafny (39 lemmas, 0 errors):

- **Per-step properties** (9) — `DoneIsStable`, allow/deny/A&D/priority step behavior
- **Stability invariants** (4) — `DoneStaysStable`, mode-specific done-implies-res invariants
- **End-to-end correctness** (10) — `AllowSome_Correctness` (res iff ContainsAllow), `DenyNone_Correctness` (res iff no ContainsDeny), `AllowAndDeny_Correctness` (res iff allow AND no deny), `Priority_Correctness` (first non-indeterminate decides)
- **Order independence** (7) — swapping adjacent effects doesn't change AllowSome, DenyNone, or AllowAndDeny decisions

To regenerate after TS changes: `npx tsx ../lemmascript/tools/src/lsc.ts regen --backend=dafny src/effect/effectorPure.ts`

## How It Works

1. Add `//@ ` annotations to TypeScript:

   ```typescript
   //@ ensures state.done === true ==> \result === state
   ```

2. Generate Lean (the generated files are checked in, but to regenerate after changing annotations):

   ```sh
   cd ../lemmascript
   npx tsx tools/src/lsc.ts gen src/effect/effectorPure.ts
   ```

   This produces `effectorPure.types.lean` and `effectorPure.def.lean`.

3. Write proof (or let `loom_solve` handle it):

   ```lean
   prove_correct pushEffectStep by
     loom_solve
   ```

4. Verify:
   ```sh
   lake build
   ```

The TypeScript is the source of truth. The Lean is generated from it. Proofs live alongside in `.proof.lean`.

## Proof Architecture

Two layers of verification:

**Layer 1 — Velvet:** The TypeScript code matches its per-step specification. The codegen generates a Velvet `method` from the annotated TS. `prove_correct` + `loom_solve` verifies per-step ensures automatically.

**Layer 2 — Pure Lean:** The specification has the desired mathematical properties (correctness, order independence). For pure functions (no loops, no mutation), the codegen generates a plain Lean `def` in `namespace Pure` (e.g., `Pure.pushEffectStep`). The Velvet method is a thin wrapper: `return Pure.pushEffectStep ...`. Sequence-level properties are proved by Lean induction over the pure function.

**Tests:** All 217 existing tests pass with verified code wired in (`npm test`).
