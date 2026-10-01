import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.Global.Scalar

/-!
# A scalar whose `0` and `1` are exact

`Scalar` reads an entry back as a real (`toReal`), and the entrywise laws say a matrix reads as
its entries do. What it has no notion of is a `0` and a `1`. Assembling a block matrix out of the
components' needs those two and no arithmetic: every entry is an existing entry, `0` or `1`,
chosen by `if`. That is this class, the two constants and that they read as `0` and `1`.

It holds at `ℝ` and at every float instance (below), because `0` and `1` are
representable in every format: nothing is rounded. There is deliberately no `+` here, since
`toReal (a + b)` is `toReal a + toReal b` only when the sum is exact (#117).
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar


-- ========================================  MAIN TYPE  ========================================= --

class ExactScalar (𝕋 : Type) [Scalar 𝕋] extends Zero 𝕋, One 𝕋 where
  toReal_zero : toReal (0 : 𝕋) = 0
  toReal_one : toReal (1 : 𝕋) = 1


/-- `ℝ` reads itself back, entry by entry. -/
instance : ExactScalar ℝ where
  toReal_zero := rfl
  toReal_one := rfl

/-- The float scalar's own `0` and `1`, which are exact in every format: `Dyadic p`,
`NearestDyadic p`, the IEEE formats and `Float` all go through this one instance. -/
instance {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] : ExactScalar 𝕋 where
  zero := Float.FloatOps.zero
  one := Float.FloatOps.one
  toReal_zero := Float.SoundFloatArithmetic.toReal_zero
  toReal_one := Float.SoundFloatArithmetic.toReal_one

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
