import CORALean.Global.Float.Instances.IEEE.Operations.RoundUp

/-!
# Rounding up never goes finer than the smallest subnormal

What separates `roundUp` from `Dyadic.roundUp`: its result is a multiple of `2 ^ qmin`, the
step of the subnormal grid, whatever it rounded, as a number of the format has to be.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem qmin_le_roundUp_exponent (d : Dyadic fmt.p) :
    fmt.qmin ≤ (roundUp d : IEEE fmt).exponent := by
  show fmt.qmin ≤ d.exponent + (gridShift d : ℤ)
  have h := le_max_right d.shift (fmt.qmin - d.exponent).toNat
  rw [← gridShift] at h
  omega

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
