module

public import CORALean.Specification.Kleene.Operations.And
public import CORALean.Specification.Kleene.Operations.Basic
public import CORALean.Specification.Kleene.Operations.Or

@[expose] public section

/-!
# `Kleene/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ====================================  `Kleene.and_assoc`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` is associative. -/
theorem Kleene.and_assoc (a b c : Kleene) : (a.and b).and c = a.and (b.and c) := by
  cases a <;> cases b <;> cases c <;> rfl


-- ====================================  `Kleene.and_comm`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` is commutative. -/
theorem Kleene.and_comm (a b : Kleene) : a.and b = b.and a := by
  cases a <;> cases b <;> rfl


-- =================================  `Kleene.and_or_distrib`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` distributes over `|`. -/
theorem Kleene.and_or_distrib (a b c : Kleene) : a.and (b.or c) = (a.and b).or (a.and c) := by
  cases a <;> cases b <;> cases c <;> rfl


-- ===================================  `Kleene.and_or_self`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Absorption: `a & (a | b) = a`. -/
theorem Kleene.and_or_self (a b : Kleene) : a.and (a.or b) = a := by
  cases a <;> cases b <;> rfl


-- ====================================  `Kleene.and_self`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` is idempotent. -/
theorem Kleene.and_self (a : Kleene) : a.and a = a := by
  cases a <;> rfl


-- ====================================  `Kleene.code_and`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` is the minimum of the stored codes `False(0) < Unknown(1) < True(2)`. -/
theorem Kleene.code_and (a b : Kleene) : (a.and b).code = min a.code b.code := by
  cases a <;> cases b <;> rfl


-- ====================================  `Kleene.code_not`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `~` reverses the stored codes. -/
theorem Kleene.code_not (a : Kleene) : a.not.code = 2 - a.code := by
  cases a <;> rfl


-- =====================================  `Kleene.code_or`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` is the maximum of the stored codes. -/
theorem Kleene.code_or (a b : Kleene) : (a.or b).code = max a.code b.code := by
  cases a <;> cases b <;> rfl


-- ==================================  `Kleene.fromBool_and`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromBool` commutes with `&` on definite values. -/
theorem Kleene.fromBool_and (a b : Bool) :
    Kleene.fromBool (a && b) = (Kleene.fromBool a).and (Kleene.fromBool b) := by
  cases a <;> cases b <;> rfl


-- ==================================  `Kleene.fromBool_inj`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromBool` is injective. -/
theorem Kleene.fromBool_inj (a b : Bool) (h : Kleene.fromBool a = Kleene.fromBool b) :
    a = b := by
  cases a <;> cases b <;> first | rfl | cases h


-- ==================================  `Kleene.fromBool_not`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromBool` commutes with `~` on definite values. -/
theorem Kleene.fromBool_not (a : Bool) : Kleene.fromBool (!a) = (Kleene.fromBool a).not := by
  cases a <;> rfl


-- ===================================  `Kleene.fromBool_or`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromBool` commutes with `|` on definite values. -/
theorem Kleene.fromBool_or (a b : Bool) :
    Kleene.fromBool (a || b) = (Kleene.fromBool a).or (Kleene.fromBool b) := by
  cases a <;> cases b <;> rfl


-- =====================================  `Kleene.not_and`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- De Morgan: `~(a & b) = ~a | ~b`. -/
theorem Kleene.not_and (a b : Kleene) : (a.and b).not = a.not.or b.not := by
  cases a <;> cases b <;> rfl


-- =====================================  `Kleene.not_not`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `~~a = a`. -/
theorem Kleene.not_not (a : Kleene) : a.not.not = a := by
  cases a <;> rfl


-- ==================================  `Kleene.not_ofBoolUnk`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Negation negates the Boolean part and keeps the unknown part. -/
theorem Kleene.not_ofBoolUnk (b u : Bool) :
    (Kleene.ofBoolUnk b u).not = Kleene.ofBoolUnk (!b) u := by
  cases b <;> cases u <;> rfl


-- =====================================  `Kleene.not_or`  ====================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- De Morgan: `~(a | b) = ~a & ~b`. -/
theorem Kleene.not_or (a b : Kleene) : (a.or b).not = a.not.and b.not := by
  cases a <;> cases b <;> rfl


-- ===========================  `Kleene.ofBoolUnk_toBool_isUnknown`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Splitting a value into its Boolean and unknown parts and joining them is the identity. -/
theorem Kleene.ofBoolUnk_toBool_isUnknown (a : Kleene) :
    Kleene.ofBoolUnk a.toBool a.isUnknown = a := by
  cases a <;> rfl


-- =================================  `Kleene.or_and_distrib`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` distributes over `&`. -/
theorem Kleene.or_and_distrib (a b c : Kleene) : a.or (b.and c) = (a.or b).and (a.or c) := by
  cases a <;> cases b <;> cases c <;> rfl


-- ===================================  `Kleene.or_and_self`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Absorption: `a | (a & b) = a`. -/
theorem Kleene.or_and_self (a b : Kleene) : a.or (a.and b) = a := by
  cases a <;> cases b <;> rfl


-- ====================================  `Kleene.or_assoc`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` is associative. -/
theorem Kleene.or_assoc (a b c : Kleene) : (a.or b).or c = a.or (b.or c) := by
  cases a <;> cases b <;> cases c <;> rfl


-- =====================================  `Kleene.or_comm`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` is commutative. -/
theorem Kleene.or_comm (a b : Kleene) : a.or b = b.or a := by
  cases a <;> cases b <;> rfl


-- =====================================  `Kleene.or_self`  ===================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` is idempotent. -/
theorem Kleene.or_self (a : Kleene) : a.or a = a := by
  cases a <;> rfl


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
