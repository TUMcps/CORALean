import CORALean.Global.Float.Instances.FixedPoint.Operations.ExactAdd
import CORALean.Global.Float.Instances.FixedPoint.Theorems.ToRealMk

/-!
# Addition is exact

`exactAdd` agrees with ℝ on the nose: it is exactly `div_add_div`'s
cross-multiplied sum read back. What
`SoundFloatArithmetic.add_le_addUp`/`addDown_le_add` compose with the
rounding step to get.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.FixedPoint

variable {f : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_exactAdd (a b : FixedPoint f) :
    toReal (exactAdd a b) = toReal a + toReal b := by -- --- PROOF ---
  have ha : (10 : ℝ) ^ a.d ≠ 0 := by positivity
  have hb : (10 : ℝ) ^ b.d ≠ 0 := by positivity
  rw [exactAdd, toReal_mk, toReal_def, toReal_def, pow_add, div_add_div _ _ ha hb]
  push_cast
  ring

end CORALean.Float.FixedPoint


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
