import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealHalf
import CORALean.Global.Float.Instances.IEEE.Operations.Half

/-!
# Halving is exact

It is `Dyadic.half` on the same pair, which is why it may leave the grid.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_half (x : IEEE fmt) : (half x).toReal = x.toReal / 2 :=
  Dyadic.toReal_half x.toDyadic

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
