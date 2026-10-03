import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.Global.Float.Sqrt

/-!
# The square root's machine enclosure

`sqrtDown` below, `sqrtUp` above, computed by `p` Newton steps
(`Global/Float/Sqrt`), sound for any `p`.
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

/-- `sqrtDown` below, `sqrtUp` above, with `p` Newton steps. -/
def rootEnclosure (p : ℕ) : Enclosure 𝕋 where
  lo a := sqrtDown p a
  hi a := sqrtUp p a

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
