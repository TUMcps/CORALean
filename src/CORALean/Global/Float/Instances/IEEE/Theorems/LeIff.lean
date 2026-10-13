import CORALean.Global.Float.Instances.Dyadic.Theorems.LeIff
import CORALean.Global.Float.Instances.IEEE.Operations.Le

/-!
# Comparison is exact

Both directions, read off `Dyadic.le_iff`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_iff (a b : IEEE fmt) : le a b = true ↔ a.toReal ≤ b.toReal :=
  Dyadic.le_iff a.toDyadic b.toDyadic

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
