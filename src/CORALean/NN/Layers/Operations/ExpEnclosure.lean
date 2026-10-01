import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.Global.Float.Exp

/-!
# The exponential enclosure

`Float.expDown` below, `Float.expUp` above, at reduction depth `k`. `expUp` bounds `exp a` only
for `a ≤ 2ⁿ/2`, so unlike the sigmoid, which gets both ends from `expDown`, the enclosure is not
total: `expRelaxation_sound` asks of a box that its right end is under that bound.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `expDown` below, `expUp` above, at reduction depth `k`. -/
def expEnclosure (k : ℕ) : Enclosure 𝕋 where
  lo a := expDown k a
  hi a := expUp k a

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
