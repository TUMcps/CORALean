module

public import CORALean.Specification.FourValued.Operations.And
public import CORALean.Specification.FourValued.Operations.Basic
public import CORALean.Specification.FourValued.Operations.Not
public import CORALean.Specification.FourValued.Operations.Or
public import CORALean.Specification.Kleene.Operations.And
public import CORALean.Specification.Kleene.Operations.Basic
public import CORALean.Specification.Kleene.Operations.Or

@[expose] public section

/-!
# `FourValued/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


namespace CORALean


-- ==================================  `FourValued.and_assoc`  ================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` is associative. -/
theorem FourValued.and_assoc (a b c : FourValued) : (a.and b).and c = a.and (b.and c) := by
  cases a <;> cases b <;> cases c <;> rfl


-- ==================================  `FourValued.and_comm`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` is commutative. -/
theorem FourValued.and_comm (a b : FourValued) : a.and b = b.and a := by
  cases a <;> cases b <;> rfl


-- ===================================  `FourValued.and_ff`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `False` absorbs under `&`. -/
theorem FourValued.and_ff (a : FourValued) : a.and .ff = .ff := by
  cases a <;> rfl


-- ===================================  `FourValued.and_ii`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An inconclusive operand makes `&` inconclusive unless the result is already false. -/
theorem FourValued.and_ii (a : FourValued) :
    a.and .ii = if a = .ff then .ff else .ii := by
  cases a <;> rfl


-- ==============================  `FourValued.and_or_distrib_ne`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` does not distribute over `|`: `Unknown & (Inconclusive | True) = Unknown`. -/
theorem FourValued.and_or_distrib_ne :
    FourValued.uu.and (FourValued.ii.or .tt) ≠
      (FourValued.uu.and .ii).or (FourValued.uu.and .tt) := nofun


-- ===============================  `FourValued.and_or_self_ne`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Absorption fails: `Unknown & (Unknown | Inconclusive)` is not `Unknown`. -/
theorem FourValued.and_or_self_ne :
    FourValued.uu.and (FourValued.uu.or .ii) ≠ .uu := nofun


-- ==================================  `FourValued.and_self`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `&` is idempotent. -/
theorem FourValued.and_self (a : FourValued) : a.and a = a := by
  cases a <;> rfl


-- ===================================  `FourValued.and_tt`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `True` is the unit of `&`. -/
theorem FourValued.and_tt (a : FourValued) : a.and .tt = a := by
  cases a <;> rfl


-- ===========================  `FourValued.fromBool_eq_fromKleene`  ============================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromBool` factors through the Kleene one. -/
theorem FourValued.fromBool_eq_fromKleene (b : Bool) :
    FourValued.fromBool b = FourValued.fromKleene (Kleene.fromBool b) := by
  cases b <;> rfl


-- ===============================  `FourValued.fromKleene_and`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromKleene` commutes with `&`. -/
theorem FourValued.fromKleene_and (a b : Kleene) :
    FourValued.fromKleene (a.and b) = (FourValued.fromKleene a).and (FourValued.fromKleene b) := by
  cases a <;> cases b <;> rfl


-- ============================  `FourValued.fromKleene_eq_ff_iff`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromKleene` gives `False` only for `False`. -/
theorem FourValued.fromKleene_eq_ff_iff (k : Kleene) :
    FourValued.fromKleene k = FourValued.ff ↔ k = Kleene.ff := by
  cases k <;> simp [FourValued.fromKleene]


-- ============================  `FourValued.fromKleene_eq_tt_iff`  ============================= --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromKleene` gives `True` only for `True`. -/
theorem FourValued.fromKleene_eq_tt_iff (k : Kleene) :
    FourValued.fromKleene k = FourValued.tt ↔ k = Kleene.tt := by
  cases k <;> simp [FourValued.fromKleene]


-- ===============================  `FourValued.fromKleene_not`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromKleene` commutes with `~`. -/
theorem FourValued.fromKleene_not (a : Kleene) :
    FourValued.fromKleene a.not = (FourValued.fromKleene a).not := by
  cases a <;> rfl


-- ================================  `FourValued.fromKleene_or`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `fromKleene` commutes with `|`. -/
theorem FourValued.fromKleene_or (a b : Kleene) :
    FourValued.fromKleene (a.or b) = (FourValued.fromKleene a).or (FourValued.fromKleene b) := by
  cases a <;> cases b <;> rfl


-- ===================================  `FourValued.not_and`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- De Morgan: `~(a & b) = ~a | ~b`. -/
theorem FourValued.not_and (a b : FourValued) : (a.and b).not = a.not.or b.not := by
  cases a <;> cases b <;> rfl


-- ===================================  `FourValued.not_not`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `~~a = a`. -/
theorem FourValued.not_not (a : FourValued) : a.not.not = a := by
  cases a <;> rfl


-- ===============================  `FourValued.not_ofKleeneInc`  =============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Negation negates the Kleene part and keeps the inconclusive flag. -/
theorem FourValued.not_ofKleeneInc (k : Kleene) (inc : Bool) :
    (FourValued.ofKleeneInc k inc).not = FourValued.ofKleeneInc k.not inc := by
  cases k <;> cases inc <;> rfl


-- ===================================  `FourValued.not_or`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- De Morgan: `~(a | b) = ~a & ~b`. -/
theorem FourValued.not_or (a b : FourValued) : (a.or b).not = a.not.and b.not := by
  cases a <;> cases b <;> rfl


-- =====================  `FourValued.ofKleeneInc_toKleene_isInconclusive`  ===================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Splitting a value into its Kleene part and flag and joining them is the identity. -/
theorem FourValued.ofKleeneInc_toKleene_isInconclusive (a : FourValued) :
    FourValued.ofKleeneInc a.toKleene a.isInconclusive = a := by
  cases a <;> rfl


-- ==============================  `FourValued.or_and_distrib_ne`  ============================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` does not distribute over `&`: `Unknown | (False & Inconclusive) = Unknown`. -/
theorem FourValued.or_and_distrib_ne :
    FourValued.uu.or (FourValued.ff.and .ii) ≠
      (FourValued.uu.or .ff).and (FourValued.uu.or .ii) := nofun


-- ===============================  `FourValued.or_and_self_ne`  ================================ --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- Absorption fails: `Unknown | (Unknown & Inconclusive)` is not `Unknown`. -/
theorem FourValued.or_and_self_ne :
    FourValued.uu.or (FourValued.uu.and .ii) ≠ .uu := nofun


-- ==================================  `FourValued.or_assoc`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` is associative. -/
theorem FourValued.or_assoc (a b c : FourValued) : (a.or b).or c = a.or (b.or c) := by
  cases a <;> cases b <;> cases c <;> rfl


-- ===================================  `FourValued.or_comm`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` is commutative. -/
theorem FourValued.or_comm (a b : FourValued) : a.or b = b.or a := by
  cases a <;> cases b <;> rfl


-- ====================================  `FourValued.or_ff`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `False` is the unit of `|`. -/
theorem FourValued.or_ff (a : FourValued) : a.or .ff = a := by
  cases a <;> rfl


-- ====================================  `FourValued.or_ii`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- An inconclusive operand makes `|` inconclusive unless the result is already true. -/
theorem FourValued.or_ii (a : FourValued) :
    a.or .ii = if a = .tt then .tt else .ii := by
  cases a <;> rfl


-- ===================================  `FourValued.or_self`  =================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `|` is idempotent. -/
theorem FourValued.or_self (a : FourValued) : a.or a = a := by
  cases a <;> rfl


-- ====================================  `FourValued.or_tt`  ==================================== --
-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---

/-- `True` absorbs under `|`. -/
theorem FourValued.or_tt (a : FourValued) : a.or .tt = .tt := by
  cases a <;> rfl


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
