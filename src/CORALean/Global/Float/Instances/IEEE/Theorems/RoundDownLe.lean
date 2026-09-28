import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealShift
import CORALean.Global.Float.Instances.IEEE.Operations.RoundDown

/-!
# Rounding down never overshoots

The floor of the shifted mantissa, shifted back, is at most the mantissa, whatever `gridShift`
is: `Dyadic.roundDown_le`'s argument at a different shift.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem roundDown_le (d : Dyadic fmt.p) :
    (roundDown d : IEEE fmt).toReal ≤ d.toReal := by -- --- PROOF ---
  show Dyadic.toReal (⟨d.mantissa / 2 ^ gridShift d, d.exponent + (gridShift d : ℤ)⟩ :
    Dyadic fmt.p) ≤ d.toReal
  rw [Dyadic.toReal_shift, Dyadic.toReal_def]
  exact mul_le_mul_of_nonneg_right
    (Int.cast_le.mpr (Int.ediv_mul_le _ (pow_ne_zero _ two_ne_zero)))
    (le_of_lt (zpow_pos two_pos _))

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
