module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Half
public import Mathlib.Algebra.Ring.CharZero

@[expose] public section

/-!
# Halving is exact

Dropping the exponent by one, which is what `SoundFloatArithmetic.toReal_half`
needs from `Dyadic`.
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_half (a : Dyadic p) : toReal (half a) = toReal a / 2 := by
  rw [toReal_def, toReal_def, half, zpow_sub₀ (two_ne_zero), zpow_one]
  ring

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
