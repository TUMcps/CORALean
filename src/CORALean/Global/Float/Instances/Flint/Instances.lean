import CORALean.Global.Float.Instances.Dyadic.Theorems.CastToRat
import CORALean.Global.Float.ToRat
import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealMkZero
import CORALean.Global.Float.Instances.Flint.Definitions.Axioms
import CORALean.Global.Float.Instances.Flint.Operations.API
import CORALean.Global.Float.Instances.Flint.Theorems.API

/-!
# `Flint p` as a sound float model

The six rounded operations are FLINT's at precision `p`, and their laws are the
six conjuncts of `trustedFlint`; the exact ones are pure Lean, and theirs are
`Dyadic`'s theorems. Computable, like `Dyadic`: an algorithm written against the
operation classes runs here once the executable links FLINT.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  INSTANCES  ========================================= --

instance {p : ℕ} : FloatOps (Flint p) where
  zero := ⟨0, 0⟩
  one := ⟨1, 0⟩
  neg := Flint.neg
  addUp := Flint.addUp p
  addDown := Flint.addDown p
  mulUp := Flint.mulUp p
  mulDown := Flint.mulDown p
  divUp := Flint.divUp p
  divDown := Flint.divDown p
  minimum := Flint.minimum
  maximum := Flint.maximum
  le := Flint.le
  half := Flint.half

/-- The rounded laws are projections of the one axiom, at this `p`. -/
instance {p : ℕ} : SoundFloatArithmetic (Flint p) where
  toReal := Flint.toReal
  toReal_neg := Flint.toReal_neg
  toReal_zero := Dyadic.toReal_mk_zero 0
  toReal_one := by
    show Dyadic.toReal (⟨1, 0⟩ : Dyadic p) = 1
    rw [Dyadic.toReal_def]
    norm_num
  add_le_addUp := Flint.trustedFlint.add_le_addUp p
  addDown_le_add := Flint.trustedFlint.addDown_le_add p
  mul_le_mulUp := Flint.trustedFlint.mul_le_mulUp p
  mulDown_le_mul := Flint.trustedFlint.mulDown_le_mul p
  div_le_divUp := Flint.trustedFlint.div_le_divUp p
  divDown_le_div := Flint.trustedFlint.divDown_le_div p
  toReal_minimum := Flint.toReal_minimum
  toReal_maximum := Flint.toReal_maximum
  toReal_le_of_le := Flint.toReal_le_of_le
  toReal_half := Flint.toReal_half

/-- The mantissa and exponent read back from FLINT, decoded exactly: the same
`toDyadic` `toReal` reads, so `trustedFlint` is not involved. -/
instance {p : ℕ} : ToRat (Flint p) where
  toRat a := a.toDyadic.toRat
  toReal_toRat a := Dyadic.cast_toRat a.toDyadic
  isNaN _ := false

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
