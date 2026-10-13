import CORALean.Global.ExactScalar

/-!
# A scalar whose negation is exact

`ExactScalar` has `0` and `1` and, deliberately, no arithmetic. Negation is the one operation
that is exact in every format (sign is a bit), so a method that only flips signs, CORA's `uminus`,
can ask for it without asking for a rounded `+`: this class is `-` and that it reads as `-`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar


-- ========================================  MAIN TYPE  ========================================= --

class NegScalar (𝕋 : Type) [Scalar 𝕋] extends Neg 𝕋 where
  toReal_neg (a : 𝕋) : toReal (-a) = -toReal a

/-- `ℝ` negates itself. -/
instance : NegScalar ℝ where
  toReal_neg _ := rfl

/-- The float scalar's own `neg`, exact in every format. -/
instance {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] : NegScalar 𝕋 where
  neg := Float.FloatOps.neg
  toReal_neg := Float.SoundFloatArithmetic.toReal_neg

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
