import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealNeg
import CORALean.Global.Float.Instances.IEEE.Operations.Neg

/-!
# Negation is exact

It is `Dyadic.neg` on the same pair.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toReal_neg (x : IEEE fmt) : (neg x).toReal = -x.toReal := Dyadic.toReal_neg x.toDyadic

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
