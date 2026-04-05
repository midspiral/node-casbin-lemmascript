import «effectorPure.types»

-- Pure.pushEffectStep is auto-generated in effectorPure.types.lean.
-- We use it here for sequence-level reasoning.

/-- Process a list of effects using the generated pure step function. -/
def foldEffects (mode : Mode) (efts : List Eft) (state : EffectState) : EffectState :=
  match efts with
  | [] => state
  | e :: rest => foldEffects mode rest (Pure.pushEffectStep mode e state)

def initState : EffectState := { res := false, recorded := false, done := false }

/-- Does the list contain an Allow? -/
def hasAllow : List Eft → Prop
  | [] => False
  | e :: rest => e = .allow ∨ hasAllow rest

/-- Does the list contain a Deny? -/
def hasDeny : List Eft → Prop
  | [] => False
  | e :: rest => e = .deny ∨ hasDeny rest

instance : DecidableEq Eft := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

instance : Decidable (hasAllow efts) := by
  induction efts with
  | nil => exact isFalse (by simp [hasAllow])
  | cons e rest ih => exact if h : e = .allow then isTrue (Or.inl h) else match ih with
    | isTrue h' => isTrue (Or.inr h')
    | isFalse h' => isFalse (by simp [hasAllow, h, h'])

instance : Decidable (hasDeny efts) := by
  induction efts with
  | nil => exact isFalse (by simp [hasDeny])
  | cons e rest ih => exact if h : e = .deny then isTrue (Or.inl h) else match ih with
    | isTrue h' => isTrue (Or.inr h')
    | isFalse h' => isFalse (by simp [hasDeny, h, h'])

/-- The first non-Indeterminate effect in the list, if any. -/
def firstDecisive : List Eft → Option Eft
  | [] => none
  | e :: rest => if e = .indeterminate then firstDecisive rest else some e

/-- Swap the elements at positions i and i+1. -/
def swapAt : List Eft → Nat → List Eft
  | [], _ => []
  | [x], _ => [x]
  | x :: y :: rest, 0 => y :: x :: rest
  | x :: rest, n + 1 => x :: swapAt rest n
