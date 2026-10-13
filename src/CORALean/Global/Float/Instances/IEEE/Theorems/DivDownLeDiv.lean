import CORALean.Global.Float.Instances.Dyadic.Theorems.DivDownLeDiv
import CORALean.Global.Float.Instances.IEEE.Operations.DivDown
import CORALean.Global.Float.Instances.IEEE.Theorems.RoundDownLe

/-!
# Division, rounded down, never overshoots

`Dyadic.divDown_le_div` for the first rounding, `roundDown_le` for the second.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem divDown_le_div (a b : IEEE fmt) (hb : 0 < b.toReal) :
    (divDown a b).toReal ≤ a.toReal / b.toReal :=
  le_trans (roundDown_le _) (Dyadic.divDown_le_div a.toDyadic b.toDyadic hb)

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
