import CORALean.Global.Float.Instances.IEEE.Operations.RoundDown

/-!
# Rounding down never goes finer than the smallest subnormal

`qmin_le_roundUp_exponent`'s counterpart: the shift is the same, only the direction differs.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem qmin_le_roundDown_exponent (d : Dyadic fmt.p) :
    fmt.qmin ≤ (roundDown d : IEEE fmt).exponent := by
  show fmt.qmin ≤ d.exponent + (gridShift d : ℤ)
  have h := le_max_right d.shift (fmt.qmin - d.exponent).toNat
  rw [← gridShift] at h
  omega

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
