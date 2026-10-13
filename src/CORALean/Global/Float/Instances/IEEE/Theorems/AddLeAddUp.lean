module

public import CORALean.Global.Float.Instances.Dyadic.Theorems.ToRealExactAdd
public import CORALean.Global.Float.Instances.IEEE.Operations.AddUp
public import CORALean.Global.Float.Instances.IEEE.Theorems.LeRoundUp

@[expose] public section

/-!
# Addition, rounded up, never undershoots

The exact sum is `Dyadic`'s, and `le_roundUp` rounds it up.
-/

-- Authors:       Claude Opus 5.5
-- Written:       28-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float.IEEE

variable {fmt : IEEEFormat}


-- =======================================  MAIN THEOREM  ======================================= --

theorem add_le_addUp (a b : IEEE fmt) : a.toReal + b.toReal ≤ (addUp a b).toReal :=
  calc a.toReal + b.toReal = (Dyadic.exactAdd a.toDyadic b.toDyadic).toReal :=
        (Dyadic.toReal_exactAdd _ _).symm
    _ ≤ _ := le_roundUp _

end CORALean.Float.IEEE


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
