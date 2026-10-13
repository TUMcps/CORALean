module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.LeDivUp
public import CORALean.Global.Float.Instances.IEEE.Operations.DivUp
public import CORALean.Global.Float.Instances.IEEE.Theorems.LeRoundUp

@[expose] public section

/-!
# Division, rounded up, never undershoots

`Dyadic.le_divUp` for the first rounding, `le_roundUp` for the second.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem div_le_divUp (a b : IEEE fmt) (hb : 0 < b.toReal) :
    a.toReal / b.toReal ≤ (divUp a b).toReal :=
  le_trans (Dyadic.le_divUp a.toDyadic b.toDyadic hb) (le_roundUp _)

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
