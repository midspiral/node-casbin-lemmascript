/**
 * Pure extraction of keyGet from builtinOperators.ts.
 * Returns the matched part after the wildcard position.
 * Verified with LemmaScript.
 */

export function keyGet(key1: string, key2: string): string {
  //@ type pos int
  //@ ensures key2.indexOf('*') === -1 ==> \result === ''
  //@ ensures key1.length <= key2.indexOf('*') ==> \result === ''
  //@ ensures key2.indexOf('*') >= 0 && key2.indexOf('*') <= key1.length && key2.indexOf('*') <= key2.length && key1.slice(0, key2.indexOf('*')) !== key2.slice(0, key2.indexOf('*')) ==> \result === ''

  const pos = key2.indexOf('*');
  if (pos === -1) {
    return '';
  }
  if (key1.length > pos) {
    if (key1.slice(0, pos) === key2.slice(0, pos)) {
      return key1.slice(pos, key1.length);
    }
  }
  return '';
}
