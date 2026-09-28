import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealShift
import CORALean.Global.Float.Instances.IEEE.Operations.RoundUp

/-!
# Rounding up never undershoots

`Dyadic.le_roundUp`'s argument, which never used how many bits were dropped: the ceiling of the
shifted mantissa, shifted back, is at least the mantissa, whatever `gridShift` is.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_roundUp (d : Dyadic fmt.p) :
    d.toReal ≤ (roundUp d : IEEE fmt).toReal := by -- --- PROOF ---
  have h : d.mantissa ≤ -(-d.mantissa / 2 ^ gridShift d) * 2 ^ gridShift d := by
    rw [neg_mul, le_neg]
    exact Int.ediv_mul_le _ (pow_ne_zero _ two_ne_zero)
  show d.toReal ≤ Dyadic.toReal (⟨-(-d.mantissa / 2 ^ gridShift d),
    d.exponent + (gridShift d : ℤ)⟩ : Dyadic fmt.p)
  rw [Dyadic.toReal_shift, Dyadic.toReal_def]
  exact mul_le_mul_of_nonneg_right (Int.cast_le.mpr h) (le_of_lt (zpow_pos two_pos _))

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
