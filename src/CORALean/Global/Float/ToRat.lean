import CORALean.Global.Float.SoundFloatArithmetic
import Mathlib.Data.Rat.Cast.Defs

/-!
# The exact rational a float denotes

`toRat` decodes a scalar into ℚ, computably and exactly, and `toReal_toRat` says
it is the number `toReal` reads. What an algorithm needs it for is a decision
the rounded operations cannot make: whether `(tFinal - tStart) / timeStep` is a
natural number, CORA's integer-steps check, taken exactly rather than to a
tolerance.

A class of its own, beside `SoundFloatArithmetic` rather than inside it, since
ℝ, an instance of that class, has no computable rational to decode to; every
machine format has one, and each instance proves the equation from its own
`toReal`. ℚ rather than a dyadic, since `FixedPoint` is decimal.
-/

-- Authors:       Tobias Ladner
-- Written:       30-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- An exact, computable decoding into ℚ, agreeing with `toReal`. -/
class ToRat (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] where
  toRat : 𝕋 → ℚ
  toReal_toRat (x : 𝕋) : ((toRat x : ℚ) : ℝ) = SoundFloatArithmetic.toReal x

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
