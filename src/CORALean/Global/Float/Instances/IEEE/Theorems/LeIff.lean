import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff
import CORALean.Global.Float.Instances.IEEE.Operations.Le

/-!
# Comparison is exact

Both directions, read off `Dyadic.le_iff`.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_iff (a b : IEEE fmt) : le a b = true ↔ a.toReal ≤ b.toReal :=
  Dyadic.le_iff a.toDyadic b.toDyadic

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
