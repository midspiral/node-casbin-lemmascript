/**
 * Pure extraction of arrayEquals from util.ts.
 * Verified with LemmaScript.
 */

export function arrayEquals(a: string[], b: string[]): boolean {
  //@ type i nat
  //@ type aLen nat
  //@ type bLen nat
  //@ ensures implies($result === true, a.length === b.length)
  //@ ensures implies($result === true, forall((k: nat) => implies(k < a.length, a[k] === b[k])))
  //@ ensures implies($result === false && a.length === b.length, exists((k: nat) => k < a.length && a[k] !== b[k]))

  const aLen = a.length;
  const bLen = b.length;
  if (aLen !== bLen) {
    return false;
  }

  let result = true;
  let i = 0;
  while (i < aLen) {
    //@ invariant i <= aLen
    //@ invariant implies(result === true, forall((k: nat) => implies(k < i, a[k] === b[k])))
    //@ invariant implies(result === false, exists((k: nat) => k < aLen && a[k] !== b[k]))
    //@ done_with result === false || !(i < aLen)
    //@ decreases aLen - i
    if (a[i] !== b[i]) {
      result = false;
      break;
    }
    i = i + 1;
  }
  return result;
}
