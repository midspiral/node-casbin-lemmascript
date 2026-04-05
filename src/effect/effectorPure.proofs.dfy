// Proofs for Casbin effect processing
// Ported from node-casbin-node/lemmafit/dafny/Effector.dfy
// and casbin-lemmascript/src/effect/effectorPure.proof.lean

include "effectorPure.dfy"

// ============================================================================
// Helper definitions
// ============================================================================

function InitState(): EffectState {
  EffectState(false, false, false)
}

// Pure recursive fold over effects (functional equivalent of processEffects method)
function FoldEffects(mode: Mode, efts: seq<Eft>, state: EffectState): EffectState
  decreases |efts|
{
  if |efts| == 0 then state
  else FoldEffects(mode, efts[1..], pushEffectStep(mode, efts[0], state))
}

// Does the sequence contain an Allow?
predicate ContainsAllow(effects: seq<Eft>)
  decreases |effects|
{
  |effects| > 0 && (effects[0] == Eft.allow || ContainsAllow(effects[1..]))
}

// Does the sequence contain a Deny?
predicate ContainsDeny(effects: seq<Eft>)
  decreases |effects|
{
  |effects| > 0 && (effects[0] == Eft.deny || ContainsDeny(effects[1..]))
}

// Is the first non-indeterminate an Allow?
predicate FirstNonIndeterminateIsAllow(effects: seq<Eft>)
  decreases |effects|
{
  |effects| > 0 && (
    if effects[0] == Eft.allow then true
    else if effects[0] == Eft.deny then false
    else FirstNonIndeterminateIsAllow(effects[1..])
  )
}

// Final decision (accounts for DenyNone default on empty input)
function Decide(mode: Mode, effects: seq<Eft>): bool {
  var s := FoldEffects(mode, effects, InitState());
  if mode == Mode.deny && !s.done then true
  else s.res
}

// Swap elements at positions i and i+1
function SwapAt(effects: seq<Eft>, i: nat): seq<Eft>
  requires 0 <= i < |effects| - 1
{
  effects[..i] + [effects[i+1], effects[i]] + effects[i+2..]
}

// ============================================================================
// Per-step lemmas
// ============================================================================

// Once done, state never changes
lemma DoneIsStable(mode: Mode, eft: Eft, state: EffectState)
  requires state.done
  ensures pushEffectStep(mode, eft, state) == state
{}

// AllowSome: Allow → true, done
lemma AllowSome_AllowSetsTrue(state: EffectState)
  requires !state.done
  ensures pushEffectStep(Mode.allow, Eft.allow, state) == EffectState(true, true, true)
{}

// AllowSome: non-Allow → res and done unchanged
lemma AllowSome_NonAllowPreserves(eft: Eft, state: EffectState)
  requires !state.done && eft != Eft.allow
  ensures pushEffectStep(Mode.allow, eft, state).res == state.res
  ensures !pushEffectStep(Mode.allow, eft, state).done
{}

// DenyNone: Deny → false, done
lemma DenyNone_DenySetsFalse(state: EffectState)
  requires !state.done
  ensures pushEffectStep(Mode.deny, Eft.deny, state) == EffectState(false, true, true)
{}

// DenyNone: non-Deny → res=true
lemma DenyNone_NonDenyIsTrue(eft: Eft, state: EffectState)
  requires !state.done && eft != Eft.deny
  ensures pushEffectStep(Mode.deny, eft, state).res == true
  ensures !pushEffectStep(Mode.deny, eft, state).done
{}

// AllowAndDeny: Allow → true, not done
lemma AllowAndDeny_AllowSetsTrue(state: EffectState)
  requires !state.done
  ensures pushEffectStep(Mode.allow_and_deny, Eft.allow, state).res == true
  ensures !pushEffectStep(Mode.allow_and_deny, Eft.allow, state).done
{}

// AllowAndDeny: Deny → false, done
lemma AllowAndDeny_DenyOverrides(state: EffectState)
  requires !state.done
  ensures pushEffectStep(Mode.allow_and_deny, Eft.deny, state) == EffectState(false, true, true)
{}

// Priority: non-Indeterminate decides
lemma Priority_Decides(eft: Eft, state: EffectState)
  requires !state.done && eft != Eft.indeterminate
  ensures pushEffectStep(Mode.priority, eft, state).done
  ensures pushEffectStep(Mode.priority, eft, state).res == (eft == Eft.allow)
{}

// Priority: Indeterminate skips
lemma Priority_IndeterminateSkips(state: EffectState)
  requires !state.done
  ensures pushEffectStep(Mode.priority, Eft.indeterminate, state).res == state.res
  ensures !pushEffectStep(Mode.priority, Eft.indeterminate, state).done
{}

// ============================================================================
// Stability: once done, done through entire sequence
// ============================================================================

lemma DoneStaysStable(mode: Mode, effects: seq<Eft>, state: EffectState)
  requires state.done
  ensures FoldEffects(mode, effects, state) == state
  decreases |effects|
{
  if |effects| > 0 {
    DoneIsStable(mode, effects[0], state);
    DoneStaysStable(mode, effects[1..], state);
  }
}

// ============================================================================
// Mode-specific invariants through sequences
// ============================================================================

// AllowSome: done ⟹ res=true (invariant preserved through fold)
lemma AllowSome_DoneImpliesTrueFrom(effects: seq<Eft>, state: EffectState)
  requires state.done ==> state.res
  ensures var s' := FoldEffects(Mode.allow, effects, state);
          s'.done ==> s'.res
  decreases |effects|
{
  if |effects| > 0 {
    var s' := pushEffectStep(Mode.allow, effects[0], state);
    AllowSome_DoneImpliesTrueFrom(effects[1..], s');
  }
}

// DenyNone: done ⟹ res=false (invariant preserved through fold)
lemma DenyNone_DoneImpliesFalseFrom(effects: seq<Eft>, state: EffectState)
  requires state.done ==> !state.res
  ensures var s' := FoldEffects(Mode.deny, effects, state);
          s'.done ==> !s'.res
  decreases |effects|
{
  if |effects| > 0 {
    var s' := pushEffectStep(Mode.deny, effects[0], state);
    DenyNone_DoneImpliesFalseFrom(effects[1..], s');
  }
}

// AllowAndDeny: done ⟹ res=false (invariant preserved through fold)
lemma AllowAndDeny_DoneImpliesFalseFrom(effects: seq<Eft>, state: EffectState)
  requires state.done ==> !state.res
  ensures var s' := FoldEffects(Mode.allow_and_deny, effects, state);
          s'.done ==> !s'.res
  decreases |effects|
{
  if |effects| > 0 {
    var s' := pushEffectStep(Mode.allow_and_deny, effects[0], state);
    AllowAndDeny_DoneImpliesFalseFrom(effects[1..], s');
  }
}

// ============================================================================
// AllowSome end-to-end correctness
// Result is true iff at least one Allow in effects
// ============================================================================

lemma AllowSome_Correctness(effects: seq<Eft>)
  ensures Decide(Mode.allow, effects) == ContainsAllow(effects)
  decreases |effects|
{
  if |effects| == 0 {
  } else {
    var s := pushEffectStep(Mode.allow, effects[0], InitState());
    if effects[0] == Eft.allow {
      DoneStaysStable(Mode.allow, effects[1..], s);
    } else {
      AllowSome_CorrectnessFrom(effects[1..], s);
    }
  }
}

lemma AllowSome_CorrectnessFrom(remaining: seq<Eft>, state: EffectState)
  requires !state.done
  requires !state.res
  ensures FoldEffects(Mode.allow, remaining, state).res == ContainsAllow(remaining)
  decreases |remaining|
{
  if |remaining| == 0 {
  } else {
    var s' := pushEffectStep(Mode.allow, remaining[0], state);
    if remaining[0] == Eft.allow {
      DoneStaysStable(Mode.allow, remaining[1..], s');
    } else {
      AllowSome_CorrectnessFrom(remaining[1..], s');
    }
  }
}

// ============================================================================
// DenyNone end-to-end correctness
// Result is true iff no Deny in effects
// ============================================================================

lemma DenyNone_Correctness(effects: seq<Eft>)
  ensures Decide(Mode.deny, effects) == !ContainsDeny(effects)
  decreases |effects|
{
  if |effects| == 0 {
    // No effects: InitState().done == false, so Decide returns true.
    // !ContainsDeny([]) == true. ✓
  } else {
    var s := pushEffectStep(Mode.deny, effects[0], InitState());
    if effects[0] == Eft.deny {
      DoneStaysStable(Mode.deny, effects[1..], s);
    } else {
      DenyNone_CorrectnessFrom(effects[1..], s);
    }
  }
}

lemma DenyNone_CorrectnessFrom(remaining: seq<Eft>, state: EffectState)
  requires !state.done
  requires state.res
  ensures FoldEffects(Mode.deny, remaining, state).res == !ContainsDeny(remaining)
  decreases |remaining|
{
  if |remaining| == 0 {
  } else {
    var s' := pushEffectStep(Mode.deny, remaining[0], state);
    if remaining[0] == Eft.deny {
      DoneStaysStable(Mode.deny, remaining[1..], s');
    } else {
      DenyNone_CorrectnessFrom(remaining[1..], s');
    }
  }
}

// ============================================================================
// AllowAndDeny end-to-end correctness
// Result is true iff (at least one Allow) AND (no Deny)
// ============================================================================

lemma AllowAndDeny_Correctness(effects: seq<Eft>)
  ensures Decide(Mode.allow_and_deny, effects) == (ContainsAllow(effects) && !ContainsDeny(effects))
  decreases |effects|
{
  if |effects| == 0 {
  } else {
    var s := pushEffectStep(Mode.allow_and_deny, effects[0], InitState());
    if effects[0] == Eft.deny {
      DoneStaysStable(Mode.allow_and_deny, effects[1..], s);
    } else if effects[0] == Eft.allow {
      AllowAndDeny_CorrectnessFromAllow(effects[1..], s);
    } else {
      AllowAndDeny_CorrectnessFromInit(effects[1..], s);
    }
  }
}

// Helper: state after seeing at least one Allow, no Deny yet
lemma AllowAndDeny_CorrectnessFromAllow(remaining: seq<Eft>, state: EffectState)
  requires !state.done && state.res
  ensures FoldEffects(Mode.allow_and_deny, remaining, state).res == !ContainsDeny(remaining)
  decreases |remaining|
{
  if |remaining| == 0 {
  } else {
    var s' := pushEffectStep(Mode.allow_and_deny, remaining[0], state);
    if remaining[0] == Eft.deny {
      DoneStaysStable(Mode.allow_and_deny, remaining[1..], s');
    } else if remaining[0] == Eft.allow {
      AllowAndDeny_CorrectnessFromAllow(remaining[1..], s');
    } else {
      AllowAndDeny_CorrectnessFromAllow(remaining[1..], s');
    }
  }
}

// Helper: no Allow seen yet, no Deny yet
lemma AllowAndDeny_CorrectnessFromInit(remaining: seq<Eft>, state: EffectState)
  requires !state.done && !state.res
  ensures FoldEffects(Mode.allow_and_deny, remaining, state).res == (ContainsAllow(remaining) && !ContainsDeny(remaining))
  decreases |remaining|
{
  if |remaining| == 0 {
  } else {
    var s' := pushEffectStep(Mode.allow_and_deny, remaining[0], state);
    if remaining[0] == Eft.deny {
      DoneStaysStable(Mode.allow_and_deny, remaining[1..], s');
    } else if remaining[0] == Eft.allow {
      AllowAndDeny_CorrectnessFromAllow(remaining[1..], s');
    } else {
      AllowAndDeny_CorrectnessFromInit(remaining[1..], s');
    }
  }
}

// ============================================================================
// Priority end-to-end correctness
// Result is true iff the first non-Indeterminate effect is Allow
// ============================================================================

lemma Priority_Correctness(effects: seq<Eft>)
  ensures Decide(Mode.priority, effects) == FirstNonIndeterminateIsAllow(effects)
  decreases |effects|
{
  if |effects| == 0 {
  } else {
    var s := pushEffectStep(Mode.priority, effects[0], InitState());
    if effects[0] == Eft.allow {
      DoneStaysStable(Mode.priority, effects[1..], s);
    } else if effects[0] == Eft.deny {
      DoneStaysStable(Mode.priority, effects[1..], s);
    } else {
      Priority_CorrectnessFrom(effects[1..], s);
    }
  }
}

lemma Priority_CorrectnessFrom(remaining: seq<Eft>, state: EffectState)
  requires !state.done && !state.res
  ensures FoldEffects(Mode.priority, remaining, state).res == FirstNonIndeterminateIsAllow(remaining)
  decreases |remaining|
{
  if |remaining| == 0 {
  } else {
    var s' := pushEffectStep(Mode.priority, remaining[0], state);
    if remaining[0] == Eft.allow {
      DoneStaysStable(Mode.priority, remaining[1..], s');
    } else if remaining[0] == Eft.deny {
      DoneStaysStable(Mode.priority, remaining[1..], s');
    } else {
      Priority_CorrectnessFrom(remaining[1..], s');
    }
  }
}

// ============================================================================
// Order independence: swapping adjacent elements doesn't change the decision
// ============================================================================

// Swap preserves ContainsAllow
lemma ContainsAllow_SwapInvariant(effects: seq<Eft>, i: nat)
  requires 0 <= i < |effects| - 1
  ensures ContainsAllow(effects) == ContainsAllow(SwapAt(effects, i))
  decreases i
{
  if i == 0 {
    assert SwapAt(effects, 0) == [effects[1], effects[0]] + effects[2..];
    ContainsAllow_PrependEquiv(effects[0], effects[1], effects[2..]);
  } else {
    assert effects == [effects[0]] + effects[1..];
    assert SwapAt(effects, i) == [effects[0]] + SwapAt(effects[1..], i - 1);
    ContainsAllow_SwapInvariant(effects[1..], i - 1);
  }
}

lemma ContainsAllow_PrependEquiv(a: Eft, b: Eft, tail: seq<Eft>)
  ensures ContainsAllow([a, b] + tail) == ContainsAllow([b, a] + tail)
{
  assert ([a, b] + tail)[0] == a;
  assert ([a, b] + tail)[1..] == [b] + tail;
  assert ([b, a] + tail)[0] == b;
  assert ([b, a] + tail)[1..] == [a] + tail;
}

// Swap preserves ContainsDeny
lemma ContainsDeny_SwapInvariant(effects: seq<Eft>, i: nat)
  requires 0 <= i < |effects| - 1
  ensures ContainsDeny(effects) == ContainsDeny(SwapAt(effects, i))
  decreases i
{
  if i == 0 {
    assert SwapAt(effects, 0) == [effects[1], effects[0]] + effects[2..];
    ContainsDeny_PrependEquiv(effects[0], effects[1], effects[2..]);
  } else {
    assert effects == [effects[0]] + effects[1..];
    assert SwapAt(effects, i) == [effects[0]] + SwapAt(effects[1..], i - 1);
    ContainsDeny_SwapInvariant(effects[1..], i - 1);
  }
}

lemma ContainsDeny_PrependEquiv(a: Eft, b: Eft, tail: seq<Eft>)
  ensures ContainsDeny([a, b] + tail) == ContainsDeny([b, a] + tail)
{
  assert ([a, b] + tail)[0] == a;
  assert ([a, b] + tail)[1..] == [b] + tail;
  assert ([b, a] + tail)[0] == b;
  assert ([b, a] + tail)[1..] == [a] + tail;
}

// AllowSome is order-independent
lemma AllowSome_OrderIndependent(effects: seq<Eft>, i: nat)
  requires 0 <= i < |effects| - 1
  ensures Decide(Mode.allow, effects) == Decide(Mode.allow, SwapAt(effects, i))
{
  AllowSome_Correctness(effects);
  AllowSome_Correctness(SwapAt(effects, i));
  ContainsAllow_SwapInvariant(effects, i);
}

// DenyNone is order-independent
lemma DenyNone_OrderIndependent(effects: seq<Eft>, i: nat)
  requires 0 <= i < |effects| - 1
  ensures Decide(Mode.deny, effects) == Decide(Mode.deny, SwapAt(effects, i))
{
  DenyNone_Correctness(effects);
  DenyNone_Correctness(SwapAt(effects, i));
  ContainsDeny_SwapInvariant(effects, i);
}

// AllowAndDeny is order-independent
lemma AllowAndDeny_OrderIndependent(effects: seq<Eft>, i: nat)
  requires 0 <= i < |effects| - 1
  ensures Decide(Mode.allow_and_deny, effects) == Decide(Mode.allow_and_deny, SwapAt(effects, i))
{
  AllowAndDeny_Correctness(effects);
  AllowAndDeny_Correctness(SwapAt(effects, i));
  ContainsAllow_SwapInvariant(effects, i);
  ContainsDeny_SwapInvariant(effects, i);
}
