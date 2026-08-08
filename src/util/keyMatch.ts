/**
 * Pure extraction of keyMatch from builtinOperators.ts.
 * Matches key1 against pattern key2 where * is a wildcard suffix.
 * Verified with LemmaScript.
 */

export function keyMatch(key1: string, key2: string): boolean {
  //@ type pos int
  //@ ensures implies(key1 === key2, $result === true)

  const pos = key2.indexOf('*');
  if (pos === -1) {
    return key1 === key2;
  }

  if (key1.length > pos) {
    return key1.slice(0, pos) === key2.slice(0, pos);
  }

  return key1 === key2.slice(0, pos);
}
