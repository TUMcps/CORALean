module

public import CORALean.Global.Float.SoundFloatArithmetic
public import CORALean.NN.Layers.Operations.ClampUnit

@[expose] public section

/-!
# A clamped slope is at most one

`minimum` and `maximum` are exact, so the clamp reads as a value between `0` and `1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

-- not `Matrix`: its `zero` would make `FloatOps.zero` ambiguous
open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem clampUnit_le_one (c : 𝕋) : toReal (clampUnit c) ≤ 1 := by
  rw [clampUnit, toReal_maximum, toReal_minimum, toReal_zero, toReal_one]
  exact max_le zero_le_one (min_le_left _ _)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
