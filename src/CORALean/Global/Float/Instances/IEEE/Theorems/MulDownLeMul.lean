import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactMul
import CORALean.Global.Float.Instances.IEEE.Operations.MulDown
import CORALean.Global.Float.Instances.IEEE.Theorems.RoundDownLe

/-!
# Multiplication, rounded down, never overshoots

The exact product is `Dyadic`'s, and `roundDown_le` rounds it down.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem mulDown_le_mul (a b : IEEE fmt) : (mulDown a b).toReal ≤ a.toReal * b.toReal :=
  calc (mulDown a b).toReal ≤ (Dyadic.exactMul a.toDyadic b.toDyadic).toReal := roundDown_le _
    _ = a.toReal * b.toReal := Dyadic.toReal_exactMul _ _

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
