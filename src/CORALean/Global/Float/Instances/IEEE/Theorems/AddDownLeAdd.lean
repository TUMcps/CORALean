import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactAdd
import CORALean.Global.Float.Instances.IEEE.Operations.AddDown
import CORALean.Global.Float.Instances.IEEE.Theorems.RoundDownLe

/-!
# Addition, rounded down, never overshoots

The exact sum is `Dyadic`'s, and `roundDown_le` rounds it down.
-/

-- Authors:       Tobias Ladner
-- Written:       28-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem addDown_le_add (a b : IEEE fmt) : (addDown a b).toReal ≤ a.toReal + b.toReal :=
  calc (addDown a b).toReal ≤ (Dyadic.exactAdd a.toDyadic b.toDyadic).toReal := roundDown_le _
    _ = a.toReal + b.toReal := Dyadic.toReal_exactAdd _ _

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
