import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactMul
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMk

/-!
# Multiplication is exact

`exactMul` agrees with ℝ on the nose: mantissas multiply and digit counts add,
which `pow_add` reads back as the product of the two quotients. What
`SoundFloatArithmetic.mul_le_mulUp`/`mulDown_le_mul` compose with the rounding
step to get.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_exactMul (a b : FixedPoint f) :
    toReal (exactMul a b) = toReal a * toReal b := by
  rw [exactMul, toReal_mk, toReal_def, toReal_def, pow_add]
  push_cast
  ring

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
