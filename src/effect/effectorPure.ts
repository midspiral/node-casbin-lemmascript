/**
 * Pure function extraction of the Effector logic.
 * Verified with LemmaScript. The DefaultEffectorStream class calls this.
 */

export type Mode = 'allow' | 'deny' | 'allow_and_deny' | 'priority';
export type Eft = 'allow' | 'indeterminate' | 'deny';

export interface EffectState {
  res: boolean;
  recorded: boolean;
  done: boolean;
}

export function pushEffectStep(mode: Mode, eft: Eft, state: EffectState): EffectState {
  //@ ensures implies(state.done === true, $result === state)
  //@ ensures implies(state.done === false && mode === "allow" && eft === "allow", $result.res === true && $result.done === true)
  //@ ensures implies(state.done === false && mode === "deny" && eft === "deny", $result.res === false && $result.done === true)
  //@ ensures implies(state.done === false && mode === "priority" && eft !== "indeterminate", $result.done === true)
  //@ ensures implies(state.done === false && mode === "priority" && eft === "allow", $result.res === true)
  //@ ensures implies(state.done === false && mode === "priority" && eft === "deny", $result.res === false)
  //@ ensures implies(state.done === false && mode === "allow" && eft !== "allow", $result.done === false)
  //@ ensures implies(state.done === false && mode === "deny" && eft !== "deny", $result.done === false)

  if (state.done) return state;

  if (mode === 'allow') {
    if (eft === 'allow') return { res: true, recorded: true, done: true };
    return { res: state.res, recorded: false, done: false };
  }

  if (mode === 'deny') {
    if (eft === 'deny') return { res: false, recorded: true, done: true };
    return { res: true, recorded: false, done: false };
  }

  if (mode === 'allow_and_deny') {
    if (eft === 'allow') return { res: true, recorded: true, done: false };
    if (eft === 'deny') return { res: false, recorded: true, done: true };
    return { res: state.res, recorded: false, done: false };
  }

  // priority
  if (eft !== 'indeterminate') {
    return { res: eft === 'allow', recorded: true, done: true };
  }
  return { res: state.res, recorded: false, done: false };
}

export function processEffects(mode: Mode, effects: Eft[]): EffectState {
  //@ type i nat

  let state: EffectState = { res: false, recorded: false, done: false };
  let i = 0;
  while (i < effects.length) {
    //@ invariant i <= effects.length
    //@ invariant implies(mode === "allow" && state.done === true, state.res === true)
    //@ invariant implies(mode === "deny" && state.done === true, state.res === false)
    //@ decreases effects.length - i
    state = pushEffectStep(mode, effects[i], state);
    i = i + 1;
  }
  return state;
}
