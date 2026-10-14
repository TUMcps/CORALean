module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.Basic
public import CORALean.Global.Float.ToRat
public import CORALean.Global.Float.Instances.Binary64.Definitions.Axioms
public import CORALean.Global.Float.Instances.Binary64.Theorems.AddDownLeAdd
public import CORALean.Global.Float.Instances.Binary64.Theorems.DivDownLeDiv
public import CORALean.Global.Float.Instances.Binary64.Theorems.MulDownLeMul

@[expose] public section

/-!
# Native binary64 as a sound float model

The rounded operations come from `Operations`, and so do `minimum`/`maximum`,
core's `min`/`max` carrying a NaN through; `Neg.neg` and the decidable `≤` are
the machine's own. Every obligation is either assumed in `Axioms` or proved
from those assumptions in `Theorems`.

Computable, like `Dyadic`'s and unlike ℝ's: `toReal` decodes bits, so an
algorithm written against the operation classes runs at `Float` as it runs at
`Dyadic`. What separates the two backends is the one assumption, not what can
be evaluated.
-/

-- Authors:       Claude Opus 5
-- Written:       22-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  INSTANCES  ========================================= --

instance : FloatOps Float where
  zero := 0.0
  one := 1.0
  neg := Neg.neg
  addUp := Binary64.addUp
  addDown := Binary64.addDown
  mulUp := Binary64.mulUp
  mulDown := Binary64.mulDown
  divUp := Binary64.divUp
  divDown := Binary64.divDown
  minimum := Binary64.minimum
  maximum := Binary64.maximum
  le := fun a b => decide (a ≤ b)
  half := Binary64.half

/-- Every field is a conjunct of the single axiom, `toReal_le_of_le` after one
step: the class asks for a `Bool` where `TrustedHardware` states `≤`, and
`of_decide_eq_true` turns the one into the other. -/
instance : SoundFloatArithmetic Float where
  toReal := Binary64.toReal
  toReal_neg := Binary64.trustedHardware.toReal_neg
  toReal_zero := Binary64.trustedHardware.toReal_zero
  toReal_one := Binary64.trustedHardware.toReal_one
  add_le_addUp := Binary64.trustedHardware.add_le_addUp
  addDown_le_add := Binary64.addDown_le_add
  mul_le_mulUp := Binary64.trustedHardware.mul_le_mulUp
  mulDown_le_mul := Binary64.mulDown_le_mul
  div_le_divUp := Binary64.trustedHardware.div_le_divUp
  divDown_le_div := Binary64.divDown_le_div
  toReal_minimum := Binary64.trustedHardware.toReal_min
  toReal_maximum := Binary64.trustedHardware.toReal_max
  toReal_le_of_le h := Binary64.trustedHardware.toReal_le_of_le _ _ (of_decide_eq_true h)
  toReal_half := Binary64.trustedHardware.toReal_half

/-- The bits, decoded exactly: `toReal` is defined through the same `toDyadic`,
so this is proved, not assumed — `trustedHardware` is not involved. -/
instance : ToRat Float where
  toRat x := (Binary64.toDyadic x).toRat
  toReal_toRat x := Dyadic.cast_toRat (Binary64.toDyadic x)
  isNaN := Float.isNaN

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
