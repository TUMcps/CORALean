module

public import CORALean.Global.Float.Instances.FixedPoint.Operations.Half
public import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealDef

@[expose] public section

/-!
# Halving is exact

`m / 10 ^ d / 2 = 5m / 10 ^ (d + 1)`, which is what
`SoundFloatArithmetic.toReal_half` needs from `FixedPoint`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_half (x : FixedPoint f) : toReal (half x) = toReal x / 2 := by
  rw [toReal_def, toReal_def, half, pow_succ]
  push_cast
  ring

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
