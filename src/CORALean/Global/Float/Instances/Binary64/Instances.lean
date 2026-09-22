import CORALean.Global.Float.Instances.Binary64.Theorems.API

/-!
# Native binary64 as a sound float model

The rounded operations come from `Operations`, the exact ones straight from
core — `Neg.neg`, `min`, `max` and the decidable `≤` are the machine's own — and
every obligation is either assumed in `Axioms` or proved from those assumptions
in `Theorems`.

Computable, like `Dyadic`'s and unlike ℝ's: `toReal` decodes bits, so an
algorithm written against the operation classes runs at `Float` as it runs at
`Dyadic`. What separates the two backends is the one assumption, not what can
be evaluated.
-/

-- Authors:       Tobias Ladner
-- Written:       22-September-2026
-- Last update:   ---
-- Last revision: ---


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
  minimum := min
  maximum := max
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

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
