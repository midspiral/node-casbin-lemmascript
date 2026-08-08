/**
 * Pure extraction of the filtering logic from Model.getFilteredPolicy.
 * Given a rule and field values starting at fieldIndex, returns whether the rule matches.
 * Empty fieldValues are wildcards (match anything).
 * Verified with LemmaScript.
 */

export function ruleMatches(rule: string[], fieldValues: string[], fieldIndex: number, numFields: number): boolean {
  //@ type fieldIndex nat
  //@ type numFields nat
  //@ type i nat
  //@ requires numFields <= fieldValues.length
  //@ requires fieldIndex + numFields <= rule.length
  //@ ensures implies($result === false, exists((k: nat) => k < numFields && fieldValues[k] !== "" && rule[fieldIndex + k] !== fieldValues[k]))
  //@ ensures implies($result === true, forall((k: nat) => implies(k < numFields, fieldValues[k] === "" || rule[fieldIndex + k] === fieldValues[k])))

  let matched = true;
  let i = 0;
  while (i < numFields) {
    //@ decreases numFields - i
    //@ invariant i <= numFields
    //@ invariant implies(matched === true, forall((k: nat) => implies(k < i, fieldValues[k] === "" || rule[fieldIndex + k] === fieldValues[k])))
    //@ invariant implies(matched === false, exists((k: nat) => k < numFields && fieldValues[k] !== "" && rule[fieldIndex + k] !== fieldValues[k]))
    //@ done_with matched === false || !(i < numFields)
    if (fieldValues[i] !== '') {
      if (rule[fieldIndex + i] !== fieldValues[i]) {
        matched = false;
        break;
      }
    }
    i = i + 1;
  }
  return matched;
}

/**
 * Filter policies: return all rules that match the field values.
 * This is the outer loop of Model.getFilteredPolicy.
 */
export function filterPolicies(
  policies: string[][],
  fieldValues: string[],
  fieldIndex: number,
  numPolicies: number,
  numFields: number
): string[][] {
  //@ type fieldIndex nat
  //@ type numPolicies nat
  //@ type numFields nat
  //@ type i nat
  //@ requires numPolicies <= policies.length
  //@ requires numFields <= fieldValues.length
  //@ requires forall((i: nat) => implies(i < numPolicies, fieldIndex + numFields <= policies[i].length))

  let result: string[][] = [];
  let i = 0;
  while (i < numPolicies) {
    //@ decreases numPolicies - i
    //@ invariant i <= numPolicies
    if (ruleMatches(policies[i], fieldValues, fieldIndex, numFields)) {
      result = [...result, policies[i]];
    }
    i = i + 1;
  }
  return result;
}
