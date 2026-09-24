import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.NN.Layers.Operations.ClampUnit

/-!
# A clamped slope is nonnegative

`maximum` is exact, so the clamp is at least the stored `zero`, which reads as `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

-- not `Matrix`: its `zero` would make `FloatOps.zero` ambiguous
open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem clampUnit_nonneg (c : 𝕋) : 0 ≤ toReal (clampUnit c) := by
  rw [clampUnit, toReal_maximum, toReal_zero]
  exact le_max_left _ _

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
