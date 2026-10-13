import CORALean.Global.Float.SoundFloatArithmetic
import Mathlib.Data.Rat.Cast.Defs

/-!
# The exact rational a float denotes

`toRat` decodes a scalar into ℚ, computably and exactly, and `toReal_toRat` says
it is the number `toReal` reads. What an algorithm needs it for is a decision
the rounded operations cannot make: whether `(tFinal - tStart) / Δt` is a
natural number, CORA's integer-steps check, taken exactly rather than to a
tolerance.

A class of its own, beside `SoundFloatArithmetic` rather than inside it, since
ℝ, an instance of that class, has no computable rational to decode to; every
machine format has one, and each instance proves the equation from its own
`toReal`. ℚ rather than a dyadic, since `FixedPoint` is decimal.

A hardware NaN decodes, as any bit pattern does, to the finite `1.5 · 2 ^ 1024`, so `toRat`
never says a value is not a number; `isNaN` does, and is `false` at a format without NaN.
A decision in ℚ that is not a tuning choice tests it first (`NoNaN.lean` tests a result).
-/

-- Authors:       Claude Opus 5.5
-- Written:       30-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- An exact, computable decoding into ℚ, agreeing with `toReal`. -/
class ToRat (𝕋 : Type) [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] where
  toRat : 𝕋 → ℚ
  toReal_toRat (x : 𝕋) : ((toRat x : ℚ) : ℝ) = SoundFloatArithmetic.toReal x
  /-- Native `Float.isNaN`; `false` at a format with no NaN. A NaN's `toRat` is a
  number like another, so this is the only way to tell it apart. -/
  isNaN : 𝕋 → Bool

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
