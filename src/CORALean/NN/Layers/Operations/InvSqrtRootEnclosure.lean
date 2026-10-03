import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.Global.Float.Sqrt

/-!
# The inverse square root's machine enclosure

`x ↦ 1/√(max x 1)` (`Real.invSqrt`) from the root: the clamp is exact, `sqrtUp` in the divisor
gives a lower bound and `sqrtDown` floored at `1` (the true root is at least `1`) an upper one.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `1/√(max x 1)` from below and above, with `p` Newton steps. -/
def invSqrtRootEnclosure (p : ℕ) : Enclosure 𝕋 where
  lo a := divDown one (sqrtUp p (maximum a one))
  hi a := divUp one (maximum one (sqrtDown p (maximum a one)))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
