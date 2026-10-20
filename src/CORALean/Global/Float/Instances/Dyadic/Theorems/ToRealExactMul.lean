module

public import CORALean.Global.Float.Instances.Dyadic.Operations.Basic
public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealDef
public import Mathlib.Algebra.Ring.CharZero

@[expose] public section

/-!
# Multiplication is exact

`exactMul` agrees with ℝ on the nose: exponents add and mantissas multiply,
which is exactly what `zpow_add₀` reads back. What
`SoundFloatArithmetic.mul_le_mulUp`/`mulDown_le_mul` compose with the rounding
step to get.

## Inputs
* `a` – first factor
* `b` – second factor

## Hypotheses
* none

## Conclusion
* the exact product denotes the real product
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.Dyadic

variable {p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_exactMul (a b : Dyadic p) :
    toReal (exactMul a b) = toReal a * toReal b := by
  rw [toReal_def, toReal_def, toReal_def, exactMul, Int.cast_mul, zpow_add₀ (two_ne_zero)]
  ring

end CORALean.Float.Dyadic


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
